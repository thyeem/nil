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
-- , Wmap
-- , circuit'from'ast
-- , v'fromWmap
-- , wmap'fromList
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
  , member
  , (!?)
  )
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Nil.Curve (Curve)
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

{- | @Arithmetic@ 'Circuit' over any data type @r@
 A circuit is simply a compound of gates and wires,
 which can be represented as a /directed acyclic graph/ or @DAG@.

 'c'symbols' == ( { symbols for @instance@ }, { symbols for @witness@ } )
-}
data Circuit r = Circuit
  { c'privs :: [String]
  , c'pubs :: [String]
  , c'gates :: [Gate r]
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

instance Show r => Pretty (Circuit r)

-- | Gates are vertices having several arithmetic operation in Circuit
data Gate r = Gate
  { g'op :: Gateop
  , g'lwire :: Wire r
  , g'rwire :: Wire r
  , g'owire :: Wire r
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

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
  | ECP' -- bop
  | EkG' -- uop
  | EPx' -- uop
  | EPy' -- uop
  | Hash' -- uop
  | GT' -- rop
  | LT' -- rop
  | GE' -- rop
  | LE' -- rop
  | EQ' -- rop
  | NE' -- rop
  deriving (Eq, Ord, Show, Generic, NFData, ToJSON)

{- | Wires are edges connecting gates each other with coefficients
 Two input wires (left, right) and one output wire in each gate
-}
data Wire r = Wire
  { w'key :: String
  , w'expr :: String
  , w'recip :: Bool
  , w'val :: r
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

-- | Map from string keys to wires
type Wmap r = Map String (Wire r)

-- | Data type for collecting gates while traversing AST
type State r = ([Gate r], Wmap r)

(<~) :: Ord k => Map k a -> (k, a) -> Map k a
(<~) = flip (uncurry insert)
{-# INLINE (<~) #-}

(~>) :: (Ord k, Show k) => Map k a -> k -> a
(~>) map key =
  fromMaybe (die $ "Error, not found key: " ++ show key) (map !? key)
{-# INLINE (~>) #-}

-- | Put a wire to the wire map
(<~~) :: Wmap r -> Wire r -> Wmap r
(<~~) wmap wire = wmap <~ (w'key wire, wire)
{-# INLINE (<~~) #-}

-- | Replace wires in a Wamp with what previously bound wires
(~~>) :: Wmap r -> Wire r -> Wire r
(~~>) wmap wire@Wire {..}
  | const'wirep wire = wire
  | otherwise = wmap ~> w'key
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
set'key :: String -> Wire r -> Wire r
set'key key wire@Wire {} = wire {w'key = key}
{-# INLINE set'key #-}

-- | Set a given wire's value
set'val :: r -> Wire r -> Wire r
set'val val wire@Wire {} = wire {w'val = val}
{-# INLINE set'val #-}

-- | Set a given wire's recip flag
set'recip :: Bool -> Wire r -> Wire r
set'recip flag wire@Wire {} = wire {w'recip = flag}

-- | Set a given wire's expression
set'expr :: String -> Wire r -> Wire r
set'expr expr wire@Wire {} = wire {w'expr = expr}

-- | Get a unit-value const wire
unit'const :: Num r => Wire r
unit'const = Wire const'key const'key False 1
{-# INLINE unit'const #-}

-- | Get a unit-value wire with a given key
unit'var :: Num r => String -> Wire r
unit'var key = Wire key key False 1
{-# INLINE unit'var #-}

-- | Get a const wire of a given value
val'const :: Num r => r -> Wire r
val'const val = set'val val unit'const
{-# INLINE val'const #-}

-- | Predicate for a const-wire
const'wirep :: Wire r -> Bool
const'wirep Wire {..} = w'key == const'key
{-# INLINE const'wirep #-}

-- | Predicate for a out-wire
out'wirep :: Wire r -> Bool
out'wirep Wire {..} = case w'key of
  x : _
    | x == out'prefix -> True
    | otherwise -> False
  _ -> False
{-# INLINE out'wirep #-}

{- | Check if both gate input wires are extended wires
 and'ext'wirep :: Integral a => Wmap a -> Gate a -> Bool
 and'ext'wirep wmap = and' $ ext'wirep . (wmap ~~>)
-}

{- | Check if one of gate input wires is an extended wire
 xor'ext'wirep :: Integral a => Wmap a -> Gate a -> Bool
 xor'ext'wirep wmap = xor' $ ext'wirep . (wmap ~~>)
-}

{- | Check if none of gate input wires is an extended wire
 nor'ext'wirep :: Integral a => Wmap a -> Gate a -> Bool
 nor'ext'wirep wmap = nor' $ ext'wirep . (wmap ~~>)
-}

-- | Test logical operator (AND) with a predicate and input wires
and' :: (Wire r -> Bool) -> Gate r -> Bool
and' p Gate {..} = p g'lwire && p g'rwire
{-# INLINE and' #-}

-- | Test logical operator (XOR) with a predicate and input wires
xor' :: (Wire r -> Bool) -> Gate r -> Bool
xor' p g = not (and' p g) && not (nor' p g)
{-# INLINE xor' #-}

-- | Test logical operator (NOR) with a predicate and input wires
nor' :: (Wire r -> Bool) -> Gate r -> Bool
nor' p Gate {..} = not $ p g'lwire || p g'rwire
{-# INLINE nor' #-}

{- | Classfy input wires satisfying the given predicate: (pass, fail)
   The result is valid only when applied input wires hold XOR
-}
either'by :: (Wire r -> Bool) -> Gate r -> (Wire r, Wire r)
either'by p g@Gate {..}
  | xor' p g = if p g'lwire then (g'lwire, g'rwire) else (g'rwire, g'lwire)
  | otherwise =
      die $
        unwords ["Error, not XOR between:", w'key g'lwire, "and", w'key g'rwire]

{- | Construct a 'circuit' from 'AST'

 @Language -> Lexeme -> AST -> 'Arithmetic Circuit' -> R1CS -> QAP@
-}
circuit'from'ast :: Num r => AST -> Circuit r
circuit'from'ast ast =
  Circuit
    { c'pubs = pubs
    , c'privs = privs
    , c'gates = gates'from'ast (init'state pubs privs) ast
    }
 where
  (pubs, privs) = symbols'from'ast ast
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
init'state :: Num r => [String] -> [String] -> State r
init'state pubs privs =
  ( []
  , fromList $
      (\wire -> (w'key wire, wire))
        <$> (unit'var <$> pubs ++ privs)
  )
{-# INLINE init'state #-}

-- | Construct Gates by traversing AST
gates'from'ast :: Num r => State r -> AST -> [Gate r]
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
conv :: Num r => State r -> AST -> State r
conv state = \case
  Bind a@(Value V {}) b -> conv'expr state (Ebin Assign a b)
  Out Return x ->
    let (gates, wmap) = conv'expr state x
     in ( Gate
            End
            (unit'var "return")
            (g'owire . head $ gates)
            (unit'var $ out'prefix : "end")
            : gates
        , wmap
        )
  e -> die $ "Error, invalid AST found: " ++ show e
{-# INLINEABLE conv #-}

-- | Convert Expr into gates
conv'expr :: Num r => State r -> Expr -> State r
conv'expr state = \case
  Value {} -> state
  Euna Minus a -> conv'expr state (Ebin Star (Value (N (-1))) a)
  Euna o a -> conv'expr state (Ebin o (Value (N 1)) a)
  Eif a b c -> conv'if state a b c
  Rbin o a b -> conv'expr state (Ebin o a b)
  Ebin Minus a b -> conv'expr state (Ebin Plus a (Euna Minus b))
  Ebin Slash a b ->
    let [before'a, after'a, after'b] = scanl conv'expr state [a, b]
     in add'gate
          Star
          after'b
          (from'expr before'a a)
          (set'recip True . from'expr after'a $ b)
  Ebin o a b ->
    let [before'a, after'a, after'b] = scanl conv'expr state [a, b]
     in add'gate o after'b (from'expr before'a a) (from'expr after'a b)
  e -> die $ "Error, invalid expr found: " ++ show e
{-# INLINEABLE conv'expr #-}

-- | Convert if-expression into gates
conv'if :: Num r => State r -> Expr -> Expr -> Expr -> State r
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
from'expr :: Num r => State r -> Expr -> Wire r
from'expr state = \case
  Value (N n) -> val'const (fromIntegral n)
  Value (V v) -> unit'var v
  a -> g'owire . head . fst . conv'expr state $ a
{-# INLINE from'expr #-}

{- | Construct a gate with given wires and add to the given state
 This is tail-call where every recursive 'conv'expr' call ends
-}
add'gate :: Num r => Ops -> State r -> Wire r -> Wire r -> State r
add'gate op (gates, wmap) lwire rwire = case op of
  Assign -> (gates, bind'wires wmap lwire rwire)
  _ ->
    let norm wire@Wire {..}
          | out'wirep wire = wire
          | otherwise = set'recip w'recip (wmap ~~> wire)
        out'expr =
          set'expr
            (unwords ["(" ++ pretty op, w'expr lwire, w'expr rwire ++ ")"])
     in ( Gate
            (gate'op op)
            (norm lwire)
            (norm rwire)
            (out'expr . out'wire $ gates)
            : gates
        , wmap
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
  PointXY -> ECP'
  PointkG -> EkG'
  Bang -> Hash'
  Colon -> EPx'
  Semicolon -> EPy'
  Greater -> GT'
  Less -> LT'
  GreaterEq -> GE'
  LessEq -> LE'
  Equal -> EQ'
  NEqual -> NE'
  e -> die $ "Error, no gate operator for: " ++ show e
{-# INLINE gate'op #-}

-- | Generate an out wire for next gate based on a given accumulated gates
out'wire :: Num r => [Gate r] -> Wire r
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

-- | Bind two wires together and register them to Wmap a
bind'wires :: Wmap r -> Wire r -> Wire r -> Wmap r
bind'wires wmap Wire {..} rwire
  | member w'key wmap =
      die . unwords $
        ["Error, found conflicting definition for:", w'key ++ ",", w'expr]
  | otherwise =
      wmap <~ (w'key, rwire)
{-# INLINEABLE bind'wires #-}

{- | Get vector of all wire-keys used in 'circuit':
 @[const (&1), instances.., witnesses.., auxiliary symbols (~1,~2,..)..]@
 This is exactly the same as QAP bases
-}
wire'keys :: Circuit r -> [String]
wire'keys Circuit {..} =
  const'key
    : concat [sort c'pubs, sort c'privs, w'key . g'owire <$> c'gates]
{-# INLINE wire'keys #-}

-- | Clean up all of wire exprs in circuit
rm'expr :: Circuit r -> Circuit r
rm'expr circuit@Circuit {..} =
  let rm'expr'wire = set'expr mempty
      rm'expr'gate gate@Gate {..} =
        gate
          { g'lwire = rm'expr'wire g'lwire
          , g'rwire = rm'expr'wire g'rwire
          , g'owire = rm'expr'wire g'owire
          }
   in circuit {c'gates = rm'expr'gate <$> c'gates}
{-# INLINE rm'expr #-}
