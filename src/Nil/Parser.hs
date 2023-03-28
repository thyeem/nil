{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}

module Nil.Parser
  ( Expr (..),
    AST (..),
    parse,
  )
where

import Data.List (foldl')
import Nil.Lexer
  ( Keywords (..),
    Ops (..),
    Prims (..),
    Symbols (..),
    Token (..),
  )
import Nil.Utils (Pretty (..), die, splitby)

-- | Abstract Syntax Tree (AST)
data AST
  = Root AST AST AST -- topmost level of AST hierarchy
  | In Keywords Expr AST -- declaration statement
  | Out Keywords Expr -- return statement
  | Seq AST AST -- sequence of statements
  | Bind Expr Expr -- let-binding
  | Null
  deriving (Eq, Show)

-- | Expression
-- No boolean primitive, not really necessary as it can be expressed as any number
-- Here 'Evaluable' means that it can be definitely reduced to a number
data Expr
  = Value Prims -- Primitive numbers and variables
  | Euna Ops Expr -- Evaluable Unary Operator
  | Ebin Ops Expr Expr -- Evaluable Binary Operator
  | Rbin Ops Expr Expr -- Relational Binary Operator
  | Eif Expr Expr Expr -- Evaluable If-expression
  | Void
  deriving (Eq, Show)

-- | Data parsed by parsers
type Parsed a = (a, [Token])

-- | Parser: parse tokens then construct a
type Parser a = [Token] -> Parsed a

-- | Parser extension: further parse using the parsed data
type ParserX a = Parsed a -> Parsed a

-- | Construct AST by parsing given lexical units (tokens)
-- Language -> Lexemes -> [AST: Abstract Syntax Tree] -> Circuit -> R1CS -> QAP
parse :: [Token] -> AST
parse tokens
  | length stmts < 2 = die "Error, not enough statements"
  | next (head stmts) /= Kwd Language = die "Error, wrong declaration"
  | next (last stmts) /= Kwd Return = die "Error, wrong return"
  | not . evaluableAST $ ast = die "Error, unevaluable Expr used"
  | otherwise = ast
  where
    stmts = tokens `splitby` [Sym LF]
    in' = fst . parse'stmt . head $ stmts
    out' = fst . parse'stmt . last $ stmts
    opt = fst . parse'stmt <$> (init . tail $ stmts)
    opt' = foldr Seq Null opt
    ast = Root in' opt' out'

-- | Parse a sequence of actions to be carried out
-- then construct a component of AST
parse'stmt :: Parser AST
parse'stmt tokens = case next tokens of
  Kwd Language -> parse'args (munch tokens)
  Kwd Let -> parse'assign (munch tokens)
  Kwd Return -> parse'return (munch tokens)
  _ -> die $ "Error, parse error of: " ++ pretty (next tokens)

-- | Parse statement of input declaration
parse'args :: Parser AST
parse'args (Sym LParen : ts)
  | last ts /= Sym RParen = die $ "Error, syntax error of: " ++ pretty (last ts)
  | otherwise = (ast, [])
  where
    ast = foldr input Null (init ts `splitby` [Sym Comma])
    input [Kwd Pub, Prim v@(V _)] ast' = In Pub (Value v) ast'
    input [Kwd Priv, Prim v@(V _)] ast' = In Priv (Value v) ast'
    input t _ = die $ "Error, syntax error of: " ++ pretty t
parse'args t = die $ "Error, syntax error of: " ++ pretty t

-- | Parse return-statement
parse'return :: Parser AST
parse'return tokens
  | next ts /= Nil = die $ "Error, syntax error of: " ++ pretty ts
  | otherwise = (Out Return ast, ts)
  where
    (ast, ts) = expr tokens

-- | Parse statement of let-binding
parse'assign :: Parser AST
parse'assign (Prim v@(V _) : Op Assign : ts)
  | next ts' /= Nil = die $ "Error, syntax error of " <> pretty ts'
  | otherwise = (Bind (Value v) expr', ts')
  where
    (expr', ts') = expr ts
parse'assign ts = die $ "Error, syntax error of " <> pretty ts

-- | Parse all of the evaluable/relational expressions
expr :: Parser Expr
expr = expr'parser 9

-- | Parse expressions with the highest priority (factor)
factor :: Parser Expr
factor tokens = case next tokens of
  Prim a -> (Value a, munch tokens)
  Op Minus -> parse'neg (munch tokens)
  Op Colon -> parseXFromPoint (munch tokens)
  Op Semicolon -> parseYFromPoint (munch tokens)
  Op Bang -> parse'hash (munch tokens)
  Sym LParen -> parseParens (munch tokens)
  Sym LBracket -> parseECpoint (munch tokens)
  Kwd If -> parse'if (munch tokens)
  _ -> die "Error, syntax error of Expr factor"

-- | Generate 'Parser Expr' using given unary operators
parse'uop :: Ops -> Parser Expr
parse'uop op tokens
  | next tokens == Op op = die $ "Error, wrong use of: " ++ pretty op
  | otherwise = (Euna op expr', ts)
  where
    (expr', ts) = factor tokens

-- | Parse expr of a negate unary operator (-)
parse'neg :: Parser Expr
parse'neg = parse'uop Minus

-- | Parse expr of a unary operator (:) -- getting x from EC Point
parseXFromPoint :: Parser Expr
parseXFromPoint = parse'uop Colon

-- | Parse expr of a unary operator (;) -- getting y from EC Point
parseYFromPoint :: Parser Expr
parseYFromPoint = parse'uop Semicolon

-- | Parse expr of a hash unary operator (!)
parse'hash :: Parser Expr
parse'hash = parse'uop Bang

-- | Parse expr of parentheses
parseParens :: Parser Expr
parseParens tokens
  | next ts /= Sym RParen =
      die $ "Error, not balanced parentheses: " ++ pretty (Sym LParen)
  | otherwise = (expr', munch ts)
  where
    (expr', ts) = expr tokens

-- | Parse expr of EC point (square brackets, [])
parseECpoint :: Parser Expr
parseECpoint tokens
  | next ts == Sym Comma = parsePointFromXY (expr', munch ts)
  | next ts == Sym RBracket = parsePointFromG (expr', munch ts)
  | otherwise = die $ "Error, syntax error of: " ++ pretty (next ts)
  where
    (expr', ts) = expr tokens

-- | Expr parser extention: EC Point format in [x, y]
parsePointFromXY :: ParserX Expr
parsePointFromXY (expr', ts)
  | next ts' /= Sym RBracket =
      die $ "Error, not balanced square brackets: " ++ pretty (Sym LBracket)
  | otherwise = (Ebin PointXY expr' expr'', munch ts')
  where
    (expr'', ts') = expr ts

-- | Expr parser extention: EC Point format in [k]
parsePointFromG :: ParserX Expr
parsePointFromG (expr', ts) = (Euna PointkG expr', ts)

-- | Parse If-Expression
parse'if :: Parser Expr
parse'if tokens
  | next ts /= Kwd Then = die $ "Error, syntax error of: " ++ pretty (next ts)
  | otherwise = then' (Eif exprIf Void Void, munch ts)
  where
    (exprIf, ts) = expr tokens

-- | Expr parser extension: then
then' :: ParserX Expr
then' (expr', ts)
  | next ts' /= Kwd Else = die $ "Error, syntax error of: " ++ pretty (next ts')
  | otherwise = else' (Eif exprIf exprThen Void, munch ts')
  where
    (exprThen, ts') = expr ts
    (Eif exprIf _ _) = expr'

-- | Expr parser extension: else
else' :: ParserX Expr
else' (expr', ts) = (Eif exprIf exprThen exprElse, ts')
  where
    (exprElse, ts') = expr ts
    (Eif exprIf exprThen _) = expr'

-- | Generate parser extensions using binary operators
parse'bops :: [Ops] -> ParserX Expr
parse'bops ops (expr', ts) = case next ts of
  Nil -> (expr', [])
  Op o | o `elem` ops -> parse'bops ops (xBO o expr' expr'', ts')
    where
      xBO
        | o `elem` [Greater, GreaterEq, Less, LessEq, Equal, NEqual] = Rbin
        | otherwise = Ebin
      (expr'', ts') = expr'parser'from'op o (munch ts)
  _ -> (expr', ts)

-- | Choose an expr parser based on operator precedence
-- The lower value of priority, the earlier it runs
expr'parser :: Int -> Parser Expr
expr'parser priority = case priority of
  9 -> ord'eq . add'sub . mod' . mul'div . exp' . factor
  5 -> add'sub . mod' . mul'div . exp' . factor
  4 -> mod' . mul'div . exp' . factor
  3 -> mul'div . exp' . factor
  2 -> exp' . factor
  1 -> factor
  _ -> die $ "Error, no such op precedence: " ++ show priority

-- | Choose an expr parser with higher precedence than a given operator
expr'parser'from'op :: Ops -> Parser Expr
expr'parser'from'op op = case op of
  Caret -> expr'parser 1
  Star -> expr'parser 2
  Slash -> expr'parser 2
  Percent -> expr'parser 3
  Plus -> expr'parser 4
  Minus -> expr'parser 4
  Greater -> expr'parser 5
  GreaterEq -> expr'parser 5
  Less -> expr'parser 5
  LessEq -> expr'parser 5
  Equal -> expr'parser 5
  NEqual -> expr'parser 5
  _ -> die $ "Error, unexpected op: " ++ pretty op

-- | Expr parser extension: Exp (^)
exp' :: ParserX Expr
exp' = exp'var . exp'num

-- | Expr parser extension: handle numeric exponent only
exp'num :: ParserX Expr
exp'num (expr', Op Caret : Prim (N n) : ts) =
  (foldl' (Ebin Star) expr' (replicate (pred . fromIntegral $ n) expr'), ts)
exp'num a = a

-- | Expr parser extension: handle variable exponent
exp'var :: ParserX Expr
exp'var = parse'bops [Caret]

-- | Expr parser extension: Mul (*) and Div (/)
mul'div :: ParserX Expr
mul'div = parse'bops [Star, Slash]

-- | Expr parser extension: Mod (%)
mod' :: ParserX Expr
mod' = parse'bops [Percent]

-- | Expr parser extension: Add (+) and Sub (-)
add'sub :: ParserX Expr
add'sub = parse'bops [Plus, Minus]

-- | Expr parser extension: Ord (>,>=,<,<=), Eq (==) and NEq(/=)
ord'eq :: ParserX Expr
ord'eq = parse'bops [Greater, GreaterEq, Less, LessEq, Equal, NEqual]

-- | Check if given Expr is able to be evaluated or not
-- Note that Rbin is NOT evaluable since there's no boolean primitive
evaluable :: Expr -> Bool
evaluable expr' = case expr' of
  Value _ -> True
  Euna PointkG a -> evaluable' a
  Euna _ a -> evaluable a
  Ebin PointXY a b -> evaluable' a && evaluable' b
  Ebin _ a b -> evaluable a && evaluable b
  Eif c a b -> relational c && evaluable a && evaluable b
  _ -> False
  where
    evaluable' x = case x of
      Ebin PointXY _ _ -> False
      Euna PointkG _ -> False
      _ -> evaluable x

-- | Check if given Expr is described as a conditional relationship or not
relational :: Expr -> Bool
relational expr' = case expr' of
  Rbin _ a b -> evaluable a && evaluable b
  _ -> False

-- | Check if all expressions from a given AST are able to be evaluated or not
evaluableAST :: AST -> Bool
evaluableAST ast = case ast of
  Bind a b -> evaluable a && evaluable b
  In _ a b -> evaluable a && evaluableAST b
  Out _ a -> evaluable a
  Seq a b -> evaluableAST a && evaluableAST b
  Root a b c -> evaluableAST a && evaluableAST b && evaluableAST c
  Null -> True

-- | Looking ahead to get next token
next :: [Token] -> Token
next [] = Nil
next (t : _) = t

-- | Consume the very next token
munch :: [Token] -> [Token]
munch [] = die "Error, nothing to consume"
munch (_ : ts) = ts

deriving instance Pretty Expr

deriving instance Pretty AST
