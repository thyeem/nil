{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Nil.Lexer
  ( Prims (..)
  , Ops (..)
  , Keywords (..)
  , Symbols (..)
  , Token (..)
  , tokenize
  )
where

import Data.Char
  ( isAlpha
  , isAlphaNum
  , isNumber
  , ord
  )
import Data.List
  ( intercalate
  , isPrefixOf
  )
import Nil.Utils
  ( Pretty (..)
  , die
  , replace
  , strip
  )

-- | Lexicual units used in Language
data Token
  = Prim Prims
  | Op Ops
  | Kwd Keywords
  | Sym Symbols
  | Nil
  deriving (Eq, Show)

-- | Primitives of Language
data Prims
  = V String
  | N Integer
  deriving (Eq, Show)

-- | Operators available within Language
data Ops
  = Assign
  | Plus
  | Minus
  | Star
  | Slash
  | Caret
  | Percent
  | Greater
  | Less
  | GreaterEq
  | LessEq
  | Equal
  | NEqual
  | Bang
  | Colon
  | Semicolon
  | PointXY
  | PointkG
  deriving (Eq, Show)

-- | Keywords: reserved identifiers
data Keywords
  = Language
  | Pub
  | Priv
  | Let
  | If
  | Then
  | Else
  | Return
  deriving (Eq, Show)

-- | Pairs of (keyword name, keyword token)
keywords :: [(String, Keywords)]
keywords =
  [ ("language", Language)
  , ("pub", Pub)
  , ("priv", Priv)
  , ("let", Let)
  , ("if", If)
  , ("then", Then)
  , ("else", Else)
  , ("return", Return)
  ]

-- | Type that supports symbolic lexical unit
data Symbols
  = LParen
  | RParen
  | LBracket
  | RBracket
  | Comma
  | LF
  deriving (Eq, Show)

{- | Tokenize the code string, then yield a list of lexeme,
 which is the set of lexical units such as operators and operands.
 Language -> [Token: Lexical Unit] -> AST -> Circuit -> R1CS -> QAP
-}
tokenize :: String -> [Token]
tokenize language = f [] (normalize language)
 where
  f tokens [] = reverse tokens
  f tokens c@(x : xs)
    | c ~~ " " = f tokens xs
    | c ~~ "\n" = f (Sym LF : tokens) xs
    | c ~~ "," = f (Sym Comma : tokens) xs
    | c ~~ "(" = f (Sym LParen : tokens) xs
    | c ~~ ")" = f (Sym RParen : tokens) xs
    | c ~~ "[" = f (Sym LBracket : tokens) xs
    | c ~~ "]" = f (Sym RBracket : tokens) xs
    | c ~~ "!" = f (Op Bang : tokens) xs
    | c ~~ ":" = f (Op Colon : tokens) xs
    | c ~~ ";" = f (Op Semicolon : tokens) xs
    | c ~~ "+" = f (Op Plus : tokens) xs
    | c ~~ "-" = f (Op Minus : tokens) xs
    | c ~~ "*" = f (Op Star : tokens) xs
    | c ~~ "^" = f (Op Caret : tokens) xs
    | c ~~ "%" = f (Op Percent : tokens) xs
    | c ~~ "/=" = f (Op NEqual : tokens) (tail xs)
    | c ~~ "/" = f (Op Slash : tokens) xs
    | c ~~ "==" = f (Op Equal : tokens) (tail xs)
    | c ~~ "=" = f (Op Assign : tokens) xs
    | c ~~ ">=" = f (Op GreaterEq : tokens) (tail xs)
    | c ~~ ">" = f (Op Greater : tokens) xs
    | c ~~ "<=" = f (Op LessEq : tokens) (tail xs)
    | c ~~ "<" = f (Op Less : tokens) xs
    | isKeyword = f (k : tokens) ks
    | isAlpha x = f (v : tokens) vs
    | isNumber x = f (n : tokens) ns
    | otherwise = die $ "Error, unexpected char: " ++ [x]
   where
    (v, vs) = tokenize'var c
    (n, ns) = tokenize'num c
    (k, ks) = tokenize'kwd c
    isKeyword = isAlpha x && (k /= Nil)

(~~) :: (Eq a) => [a] -> [a] -> Bool
(~~) = flip isPrefixOf

-- | Clean up language string
normalize :: String -> String
normalize language = intercalate "\n" (code'only . continuation $ language)
 where
  continuation = replace "\\\n" ""
  code'only x = filter (not . blankOrComment) (strip <$> lines x)
  blankOrComment xs = null xs || xs ~~ "#"

-- | Find keyword token
tokenize'kwd :: String -> (Token, String)
tokenize'kwd = f keywords
 where
  f [] xs = (Nil, xs)
  f ((label, kwd) : kwds) xs
    | found = (Kwd kwd, xs')
    | otherwise = f kwds xs
   where
    found = xs ~~ label && stop
    stop = (not . null) xs' && (not . isAlphaNum) (head xs')
    xs' = drop (length label) xs

-- | Find variable token
tokenize'var :: String -> (Token, String)
tokenize'var = f []
 where
  f var [] = (Prim (V $ reverse var), [])
  f var c@(x : xs)
    | isAlphaNum x = f (x : var) xs
    | x == '(' = (Prim (V $ reverse var), '*' : c)
    | otherwise = (Prim (V $ reverse var), c)

-- | Find numeric token
tokenize'num :: String -> (Token, String)
tokenize'num = f 0
 where
  f num [] = (Prim (N num), [])
  f num c@(x : xs)
    | isNumber x = f sum' xs
    | isAlpha x || x == '(' = (Prim (N num), '*' : c)
    | otherwise = (Prim (N num), c)
   where
    sum' = num * 10 + fromIntegral (ord x - ord '0')

-- | Pretty printer for Token
instance Pretty Token where
  pretty = \case
    Prim (V v) -> v
    Prim (N n) -> show n
    Op Assign -> "="
    Op Plus -> "+"
    Op Minus -> "-"
    Op Star -> "*"
    Op Slash -> "/"
    Op Caret -> "^"
    Op Percent -> "%"
    Op Greater -> ">"
    Op GreaterEq -> ">="
    Op Less -> "<"
    Op LessEq -> "<="
    Op Equal -> "=="
    Op NEqual -> "/="
    Op Colon -> ":"
    Op Semicolon -> ";"
    Op Bang -> "!"
    Kwd Language -> "language"
    Kwd Pub -> "pub"
    Kwd Priv -> "priv"
    Kwd Let -> "let"
    Kwd If -> "if"
    Kwd Then -> "then"
    Kwd Else -> "else"
    Kwd Return -> "return"
    Sym LParen -> "("
    Sym RParen -> ")"
    Sym LBracket -> "["
    Sym RBracket -> "]"
    Sym Comma -> ","
    Sym LF -> "\n"
    Nil -> mempty
    a -> die $ "Error, unexpected token: " ++ show a

instance Pretty Ops where
  pretty = \case
    Plus -> "+"
    Minus -> "-"
    Star -> "*"
    Slash -> "/"
    Caret -> "^"
    Percent -> "%"
    Greater -> ">"
    GreaterEq -> ">="
    Less -> "<"
    LessEq -> "<="
    Equal -> "=="
    NEqual -> "/="
    Colon -> ":"
    Semicolon -> ";"
    Bang -> "!"
    PointXY -> "[,]"
    PointkG -> "[]"
    a -> die $ "Error, unexpected operator: " ++ show a
