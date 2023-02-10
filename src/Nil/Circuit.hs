{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Nil.Circuit where

-- ( Circuit(..)
-- , Wire(..)
-- , Gate(..)
-- , Gateop(..)
-- , W'table
-- , circuit'from'ast
-- , vec'from'table
-- , table'from'list
-- ,(!)
-- ,(!~)
-- , wire'keys
-- , statement
-- , const'wirep
-- , eval'circuit
-- ) where

import Control.DeepSeq (NFData)
import Data.Aeson (ToJSON)
import Data.List
  ( foldl'
  , sort
  )
import Data.Map
  ( Map
  , fromList
  , insert
  , keys
  , member
  , (!?)
  )
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Nil.Lexer
  ( Keywords (..)
  , Ops (..)
  , Prims (..)
  )
import Nil.Parser
  ( AST (..)
  , Expr (..)
  )
import Nil.Utils
  ( Pretty (..)
  , die
  )

{- | @Arithmetic@ 'Circuit' over a prime field @f@
 A circuit is simply a compound of gates and wires,
 which can be represented as a /directed acyclic graph/ or @DAG@.

 'c'symbols' == ( { symbols for @instance@ }, { symbols for @witness@ } )
-}
data Circuit f = Circuit
  { c'hash :: String
  , c'symbols :: ([String], [String])
  , c'gates :: [Gate f]
  }
  deriving (Eq, Show, Generic, NFData)

-- | Gates are vertices having several arithmetic operation in Circuit
data Gate f = Gate
  { g'op :: Gateop
  , g'lwire :: Wire f
  , g'rwire :: Wire f
  , g'owire :: Wire f
  }
  deriving (Eq, Show, Generic, NFData)

{- | Gate operators: Base operators (x, +) and extended extended operators (ending with ').
 Extended operators: perform operations that cannot be converted into base operators.
 Gates including extended operators also contribute to Circuit and QAP,
 however, special rules apply when evaluating
-}
data Gateop
  = End -- the final gate op
  | Mul -- base bop
  | Add -- base bop
  | Exp' -- bop
  | Mod' -- bop
  | Exy' -- bop
  | EkG' -- bop
  | Hash' -- uop
  | Px' -- uop
  | Py' -- uop
  | GT' -- rop
  | LT' -- rop
  | GE' -- rop
  | LE' -- rop
  | EQ' -- rop
  | NE' -- rop
  deriving (Eq, Ord, Show, Generic, NFData)

{- | Wires are edges connecting gates each other with coefficients
 Two input wires (left, right) and one output wire in each gate
-}
data Wire f = Wire
  { w'key :: String
  , w'val :: f
  , w'flag :: Int
  , w'expr :: String
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

-- | Look-up table for wires
type W'table f = Map String (Wire f)

-- | Data type for collecting gates while traversing AST
type State f = ([Gate f], W'table f)

-- | Get the normalized vector from W'table f
vec'from'table :: W'table f -> [f]
vec'from'table table = w'val . (table ~>) <$> keys table
{-# INLINE vec'from'table #-}

-- | Get a W'table f from List [(String, f)]
table'from'list :: Num f => [(String, f)] -> W'table f
table'from'list =
  foldr
    ( \(key, val) table ->
        table <~ (key, set'val val . unit'var $ key)
    )
    mempty
{-# INLINE table'from'list #-}

(<~) :: Ord k => Map k a -> (k, a) -> Map k a
(<~) = flip (uncurry insert)
{-# INLINE (<~) #-}

(~>) :: (Ord k, Show k) => Map k a -> k -> a
(~>) table key =
  fromMaybe (die $ "Error, not found key: " ++ show key) (table !? key)
{-# INLINE (~>) #-}

-- | Put a wire to the wire-table
(<~~) :: W'table f -> Wire f -> W'table f
(<~~) table wire = table <~ (w'key wire, wire)
{-# INLINE (<~~) #-}

-- | Replace a wire in the table with what previously bound wires
(~~>) :: W'table f -> Wire f -> Wire f
(~~>) table wire@Wire {..}
  | const'wirep wire = wire
  | otherwise = table ~> w'key
{-# INLINE (~~>) #-}

-- | The name of specially prepared wire representing constant basis
const'key :: String
const'key = "&1"
{-# INLINE const'key #-}

-- | Name prefix for auxiliary variables
out'prefix :: Char
out'prefix = '~'
{-# INLINE out'prefix #-}

-- | Set a given wire's key
set'key :: String -> Wire f -> Wire f
set'key key wire@Wire {} = wire {w'key = key}
{-# INLINE set'key #-}

-- | Set a given wire's value
set'val :: f -> Wire f -> Wire f
set'val val wire@Wire {} = wire {w'val = val}
{-# INLINE set'val #-}

-- | Set a given wire's flag
set'flag :: Int -> Wire f -> Wire f
set'flag flag wire@Wire {} = wire {w'flag = flag}

-- | Set a given wire's expression
set'expr :: String -> Wire f -> Wire f
set'expr expr wire@Wire {} = wire {w'expr = expr}

-- | Get a unit-value const wire
unit'const :: Num f => Wire f
unit'const = Wire const'key 1 0 const'key
{-# INLINE unit'const #-}

-- | Get a unit-value wire with a given key
unit'var :: Num f => String -> Wire f
unit'var key = Wire key 1 0 key
{-# INLINE unit'var #-}

-- | Get a const wire of a given value
val'const :: Num f => f -> Wire f
val'const val = set'val val unit'const
{-# INLINE val'const #-}

-- | Predicate for a const-wire
const'wirep :: Wire f -> Bool
const'wirep Wire {..} = w'key == const'key
{-# INLINE const'wirep #-}

-- | Predicate for an extended wire (representing EC-point)
ext'wirep :: Wire f -> Bool
ext'wirep Wire {..} = w'flag == 2 || w'flag == 3
{-# INLINE ext'wirep #-}

-- | Predicate for a out-wire
out'wirep :: Wire f -> Bool
out'wirep Wire {..} = case w'key of
  x : _
    | x == out'prefix -> True
    | otherwise -> False
  _ -> False
{-# INLINE out'wirep #-}

-- | Predicate for a priv-wire
inp'wirep :: Wire f -> Bool
inp'wirep wire = not (out'wirep wire) && not (const'wirep wire)
{-# INLINE inp'wirep #-}

-- | Predicate if reciprocal flag is on
recip'wirep :: Wire f -> Bool
recip'wirep wire = w'flag wire == 1
{-# INLINE recip'wirep #-}

-- | Check if both gate input wires are extended wires
and'ext'wirep :: Integral f => W'table f -> Gate f -> Bool
and'ext'wirep table = and' $ ext'wirep . (table ~~>)
{-# INLINE and'ext'wirep #-}

-- | Check if one of gate input wires is an extended wire
xor'ext'wirep :: Integral f => W'table f -> Gate f -> Bool
xor'ext'wirep table = xor' $ ext'wirep . (table ~~>)
{-# INLINE xor'ext'wirep #-}

-- | Check if none of gate input wires is an extended wire
nor'ext'wirep :: Integral f => W'table f -> Gate f -> Bool
nor'ext'wirep table = nor' $ ext'wirep . (table ~~>)
{-# INLINE nor'ext'wirep #-}

-- | Test logical operator (AND) with a predicate and input wires
and' :: (Wire f -> Bool) -> Gate f -> Bool
and' p Gate {..} = p g'lwire && p g'rwire
{-# INLINE and' #-}

-- | Test logical operator (XOR) with a predicate and input wires
xor' :: (Wire f -> Bool) -> Gate f -> Bool
xor' p g = not (and' p g) && not (nor' p g)
{-# INLINE xor' #-}

-- | Test logical operator (NOR) with a predicate and input wires
nor' :: (Wire f -> Bool) -> Gate f -> Bool
nor' p Gate {..} = not $ p g'lwire || p g'rwire
{-# INLINE nor' #-}

{- | Classfy input wires satisfying the given predicate: (pass, fail)
   The result is valid only when applied input wires hold XOR
-}
either'by :: (Wire f -> Bool) -> Gate f -> (Wire f, Wire f)
either'by p g@Gate {..}
  | xor' p g = if p g'lwire then (g'lwire, g'rwire) else (g'rwire, g'lwire)
  | otherwise =
      die $
        unwords ["Error, not XOR between:", w'key g'lwire, "and", w'key g'rwire]

{- | Construct a 'circuit' from 'AST'

 @Language -> Lexeme -> AST -> 'Arithmetic Circuit' -> R1CS -> QAP@
-}
circuit'from'ast :: Num f => AST -> Circuit f
circuit'from'ast ast =
  Circuit
    { c'hash = mempty
    , c'symbols = symbols
    , c'gates = gates'from'ast (init'state symbols) ast
    }
 where
  symbols = symbols'from'ast ast
{-# INLINEABLE circuit'from'ast #-}

-- | Get symbol names of (instances, witnesses) from AST
symbols'from'ast :: AST -> ([String], [String])
symbols'from'ast = \case
  Root ast _ _ -> go [] [] ast
  _ -> die "Error, not found root from the given AST"
 where
  go insts wits = \case
    In Pub (Value (V v)) ast' -> go (v : insts) wits ast'
    In Priv (Value (V v)) ast' -> go insts (v : wits) ast'
    Null -> (reverse $ "return" : insts, reverse wits)
    e -> die $ "Error, invalid AST used" ++ show e
{-# INLINEABLE symbols'from'ast #-}

-- | Initialize circuit parser state
init'state :: Num f => ([String], [String]) -> State f
init'state (pub, priv) =
  ([], fromList $ (\wire -> (w'key wire, wire)) <$> (pub' ++ priv'))
 where
  priv' = set'flag 5 . unit'var <$> priv
  pub' = set'flag 6 . unit'var <$> pub
{-# INLINE init'state #-}

-- | Construct Gates by traversing AST
gates'from'ast :: Num f => State f -> AST -> [Gate f]
gates'from'ast state = \case
  Root _ body out ->
    let statements = reverse $ foldl' go [] [body, out]
     in reverse . fst $ foldl' conv state statements
  _ -> die "Error, not found root from the given AST"
 where
  go seq' = \case
    Seq s@Bind {} ast -> go (s : seq') ast
    o@Out {} -> o : seq'
    Null -> seq'
    e -> die $ "Error, invalid AST used" ++ show e
{-# INLINEABLE gates'from'ast #-}

-- | Convert AST into gates
conv :: Num f => State f -> AST -> State f
conv state = \case
  Bind a@(Value V {}) b -> conv'expr state (Ebin Assign a b)
  Out Return x ->
    let (gates, table) = conv'expr state x
     in ( Gate
            End
            (unit'var "return")
            (g'owire . head $ gates)
            (unit'var $ out'prefix : "end")
            : gates
        , table
        )
  e -> die $ "Error, invalid AST found: " ++ show e
{-# INLINEABLE conv #-}

-- | Convert Expr into gates
conv'expr :: Num f => State f -> Expr -> State f
conv'expr state = \case
  Value {} -> state
  Euna Minus a -> conv'expr state (Ebin Star (Value (N (-1))) a)
  Euna o a -> conv'expr state (Ebin o (Value (N 1)) a)
  Eif a b c -> conv'if state a b c
  Rbin o a b -> conv'expr state (Ebin o a b)
  Ebin Minus a b -> conv'expr state (Ebin Plus a (Euna Minus b))
  Ebin Slash a b ->
    let [before'a, after'a, after'b] = scanl conv'expr state [a, b]
     in add'gate Star after'b (from'expr before'a a) (set'flag 1 . from'expr after'a $ b)
  Ebin o a b ->
    let [before'a, after'a, after'b] = scanl conv'expr state [a, b]
     in add'gate o after'b (from'expr before'a a) (from'expr after'a b)
  e -> die $ "Error, invalid expr found: " ++ show e
{-# INLINEABLE conv'expr #-}

-- | Convert if-expression into gates
conv'if :: Num f => State f -> Expr -> Expr -> Expr -> State f
conv'if state a b c =
  let outer = g'owire . head . fst
      [before'a, after'a, after'b, _] = scanl conv'expr state [a, b, c]
      then' = add'gate Star after'b (from'expr before'a a) (from'expr after'a b)
      else' = add'gate Star unless' (outer unless') (from'expr after'b c)
      unless' = add'gate Plus neg'if unit'const (outer neg'if)
      neg'if = add'gate Star then' (val'const (-1)) (from'expr before'a a)
   in add'gate Plus else' (outer then') (outer else')
{-# INLINEABLE conv'if #-}

-- | Convert expressions into wires based on the given state
from'expr :: Num f => State f -> Expr -> Wire f
from'expr state = \case
  Value (N n) -> val'const (fromIntegral n)
  Value (V v) -> unit'var v
  a -> g'owire . head . fst . conv'expr state $ a
{-# INLINE from'expr #-}

{- | Construct a gate with given wires and add to the given state
 This is tail-call where every recursive 'conv'expr' call ends
-}
add'gate :: Num f => Ops -> State f -> Wire f -> Wire f -> State f
add'gate op (gates, table) lwire rwire = case op of
  Assign -> (gates, bind'wires table lwire rwire)
  _ ->
    let norm wire@Wire {..}
          | out'wirep wire = wire
          | otherwise = set'flag w'flag (table ~~> wire)
        out'expr =
          set'expr
            (unwords ["(" ++ pretty op, w'expr lwire, w'expr rwire ++ ")"])
     in ( Gate
            (gate'op op)
            (norm lwire)
            (norm rwire)
            (out'expr . out'wire $ gates)
            : gates
        , table
        )
{-# INLINE add'gate #-}

-- | Get the gate operator corresponding to a given token
gate'op :: Ops -> Gateop
gate'op = \case
  -- Base gate operators
  Star -> Mul
  Plus -> Add
  -- extended gate operators
  Caret -> Exp'
  Percent -> Mod'
  PointXY -> Exy'
  PointkG -> EkG'
  Bang -> Hash'
  Colon -> Px'
  Semicolon -> Py'
  Greater -> GT'
  Less -> LT'
  GreaterEq -> GE'
  LessEq -> LE'
  Equal -> EQ'
  NEqual -> NE'
  e -> die $ "Error, no gate operator for: " ++ show e
{-# INLINE gate'op #-}

-- | Generate an out wire for next gate based on a given accumulated gates
out'wire :: Num f => [Gate f] -> Wire f
out'wire = \case
  [] -> unit'var (out'prefix : "1")
  (g : _) -> unit'var (next . w'key . g'owire $ g)
 where
  next = \case
    [] -> die "Error, wire key is empty"
    (prefix : v)
      | prefix == out'prefix -> prefix : (show . succ) (read v :: Int)
      | otherwise -> die $ "Error, not allowed wire prefix: " ++ [prefix]
{-# INLINEABLE out'wire #-}

-- | Bind two wires together and register them to W'table f
bind'wires :: W'table f -> Wire f -> Wire f -> W'table f
bind'wires table Wire {..} rwire
  | member w'key table =
      die . unwords $
        ["Error, found conflicting definition for:", w'key ++ ",", w'expr]
  | otherwise =
      table <~ (w'key, rwire)
{-# INLINEABLE bind'wires #-}

{- | Get vector of all wire-keys used in 'circuit':
 @[const (&1), instances.., witnesses.., auxiliary symbols (~1,~2,..)..]@
 This is exactly the same as QAP bases
-}
wire'keys :: Circuit f -> [String]
wire'keys Circuit {..} =
  const'key
    : concat
      [sort (fst c'symbols), sort (snd c'symbols), w'key . g'owire <$> c'gates]
{-# INLINE wire'keys #-}

-- | Pretty printer for Circuit f
instance Show f => Pretty (Circuit f)
