{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}

module Nil.Circuit
  ( Circuit (..),
    Wire (..),
    Gate (..),
    Gateop (..),
    Wmap,
    (~>),
    (<~),
    (~~>),
    (<~~),
    circuit'from'ast,
    compile'language,
    const'key,
    const'wirep,
    out'wirep,
    set'key,
    set'expr,
    set'val,
    set'recip,
    unit'const,
    unit'var,
    wire'keys,
    return'key,
    val'const,
    end'key,
    add'identity,
  )
where

import Control.DeepSeq (NFData)
import Data.Aeson (ToJSON)
import Data.List (foldl', sort)
import Data.Map (Map, fromList, insert, member, (!?))
import Data.Maybe (fromMaybe)
import Data.Store (Store)
import GHC.Generics (Generic)
import Nil.Data (NIL)
import Nil.Ecdata (BN254, Fr, G1)
import Nil.Lexer (Keywords (..), Ops (..), Prims (..), normalize, tokenize)
import Nil.Parser (AST (..), Expr (..), parse)
import Nil.Utils (Pretty (..), bytes'from'str, die, int'from'bytes, sha256)

-- | @Arithmetic@ 'Circuit' over any data type @a@
-- A circuit is simply a compound of gates and wires,
-- which can be represented as a /directed acyclic graph/ or @DAG@.
--
-- 'c'symbols' == ( { symbols for @instance@ }, { symbols for @witness@ } )
data Circuit a = Circuit
  { c'privs :: [String],
    c'pubs :: [String],
    c'gates :: [Gate a]
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

instance (Show a) => Pretty (Circuit a)

-- | Gates are vertices having several arithmetic operation in Circuit
data Gate a = Gate
  { g'op :: Gateop,
    g'lwire :: Wire a,
    g'rwire :: Wire a,
    g'owire :: Wire a
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

instance (Eq a) => Ord (Gate a) where
  x <= y = w'key (g'owire x) <= w'key (g'owire y)

-- | Gate operators: Base operators (x, +) and extended extended operators (ending with ').
-- Extended operators: perform operations that cannot be converted into base operators.
-- Gates including extended operators also contribute to Circuit and QAP,
-- however, special rules apply when evaluating
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

-- | Wires are edges connecting gates each other with coefficients
-- Two input wires (left, right) and one output wire in each gate
data Wire a = Wire
  { w'key :: String,
    w'expr :: String,
    w'recip :: Bool,
    w'val :: a
  }
  deriving (Eq, Show, Generic, NFData, ToJSON)

instance (Eq a) => Ord (Wire a) where
  x <= y = w'key x <= w'key y

deriving instance Store (Circuit Fr)

deriving instance Store (Wire Fr)

deriving instance Store Gateop

deriving instance Store (Gate Fr)

deriving instance Store (Wire (NIL BN254 Fr G1))

deriving instance Store (Gate (NIL BN254 Fr G1))

deriving instance Store (Circuit (NIL BN254 Fr G1))

-- | Map from string keys to wires
type Wmap a = Map String (Wire a)

-- | Data type for collecting gates while traversing AST
type State a = ([Gate a], Wmap a)

(<~) :: (Ord k) => Map k a -> (k, a) -> Map k a
(<~) = flip (uncurry insert)
{-# INLINE (<~) #-}

(~>) :: (Ord k, Show k) => Map k a -> k -> a
(~>) map_ key =
  fromMaybe (die $ "Error, not found key: " ++ show key) (map_ !? key)
{-# INLINE (~>) #-}

-- | Put a wire to the wire map
(<~~) :: Wmap a -> Wire a -> Wmap a
(<~~) wmap wire = wmap <~ (w'key wire, wire)
{-# INLINE (<~~) #-}

-- | Replace wires in a Wamp with what previously bound wires
(~~>) :: Wmap a -> Wire a -> Wire a
(~~>) wmap wire@Wire {..}
  | const'wirep wire = wire
  | otherwise = wmap ~> w'key
{-# INLINE (~~>) #-}

-- | The name prepared wire representing constant basis
const'key :: String
const'key = "&1"
{-# INLINE const'key #-}

-- | The name prepared wire representing end node
return'key :: String
return'key = "return"
{-# INLINE return'key #-}

-- | The name prepared wire representing outwire of end node
end'key :: String
end'key = "~end"
{-# INLINE end'key #-}

-- | Name prefix for auxiliary variables
out'prefix :: Char
out'prefix = '~'
{-# INLINE out'prefix #-}

-- | Set a given wire's key
set'key :: String -> Wire a -> Wire a
set'key key wire@Wire {} = wire {w'key = key}
{-# INLINE set'key #-}

-- | Set a given wire's value
set'val :: a -> Wire a -> Wire a
set'val val wire@Wire {} = wire {w'val = val}
{-# INLINE set'val #-}

-- | Set a given wire's recip flag
set'recip :: Bool -> Wire a -> Wire a
set'recip flag wire@Wire {} = wire {w'recip = flag}
{-# INLINE set'recip #-}

-- | Set a given wire's expression
set'expr :: String -> Wire a -> Wire a
set'expr expr wire@Wire {} = wire {w'expr = expr}
{-# INLINE set'expr #-}

-- | Get a unit-value const wire
unit'const :: (Num a) => Wire a
unit'const = Wire const'key const'key False 1
{-# INLINE unit'const #-}

-- | Get a unit-value wire with a given key
unit'var :: (Num a) => String -> Wire a
unit'var key = Wire key key False 1
{-# INLINE unit'var #-}

-- | Get a const wire of a given value
val'const :: (Num a) => a -> Wire a
val'const val = set'val val unit'const
{-# INLINE val'const #-}

-- | Predicate for a const-wire
const'wirep :: Wire a -> Bool
const'wirep Wire {..} = w'key == const'key
{-# INLINE const'wirep #-}

-- | Predicate for a out-wire
out'wirep :: Wire a -> Bool
out'wirep Wire {..} = case w'key of
  x : _
    | x == out'prefix -> True
    | otherwise -> False
  _ -> False
{-# INLINE out'wirep #-}

-- | Implicitly add identity expressions to increase number of gates
add'identity :: Int -> String -> String
add'identity n = unwords . take (n + 1) . iterate (expr . number) . normalize
  where
    number = show . int'from'bytes . sha256 . bytes'from'str
    expr x = unwords ["+", x, "-", x]
{-# INLINE add'identity #-}

-- | Derive circuit from the domain-specific language, Language
compile'language :: (Num a) => String -> Circuit a
compile'language = circuit'from'ast . parse . tokenize . add'identity 2
{-# INLINE compile'language #-}

-- | Construct a 'circuit' from 'AST'
--
-- @Language -> Lexeme -> AST -> 'Arithmetic Circuit' -> R1CS -> QAP@
circuit'from'ast :: (Num a) => AST -> Circuit a
circuit'from'ast ast =
  Circuit
    { c'pubs = pubs,
      c'privs = privs,
      c'gates = gates'from'ast (init'state pubs privs) ast
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
      Null -> (reverse $ return'key : insts, reverse wits)
      e -> die $ "Error, invalid AST used" ++ show e
{-# INLINEABLE symbols'from'ast #-}

-- | Initialize circuit parser state
init'state :: (Num a) => [String] -> [String] -> State a
init'state pubs privs =
  ( [],
    fromList $
      (\wire -> (w'key wire, wire))
        <$> (unit'var <$> pubs ++ privs)
  )
{-# INLINE init'state #-}

-- | Construct Gates by traversing AST
gates'from'ast :: (Num a) => State a -> AST -> [Gate a]
gates'from'ast state = \case
  Root _ body out ->
    let statements = reverse $ foldl' go [] [body, out]
     in reverse . fst $ foldl' parse'ast state statements
  _ -> die "Error, not found root from the given AST"
  where
    go seq' = \case
      Seq s@Bind {} ast -> go (s : seq') ast
      o@Out {} -> o : seq'
      Null -> seq'
      e -> die $ "Error, invalid AST used" ++ show e
{-# INLINEABLE gates'from'ast #-}

-- | Parse AST into gates
parse'ast :: (Num a) => State a -> AST -> State a
parse'ast state = \case
  Bind a@(Value V {}) b -> expr' state (Ebin Assign a b)
  Out Return x ->
    let (gates, wmap) = expr' state x
        latest'outwire
          | null gates = die "Error, not found gate. There must be at least one."
          | otherwise = g'owire . head $ gates
     in ( Gate
            End
            (unit'var return'key)
            latest'outwire
            (unit'var $ out'prefix : "end")
            : gates,
          wmap
        )
  e -> die $ "Error, invalid AST found: " ++ show e
{-# INLINEABLE parse'ast #-}

-- | Expr parser: convert expressions into gates
expr' :: (Num a) => State a -> Expr -> State a
expr' state = \case
  Value {} -> state
  Euna Minus a -> expr' state (Ebin Star (Value (N (-1))) a)
  Euna o a -> expr' state (Ebin o (Value (N 1)) a)
  Eif a b c -> expr'if state a b c
  Rbin o a b -> expr' state (Ebin o a b)
  Ebin Minus a b -> expr' state (Ebin Plus a (Euna Minus b))
  Ebin Slash a b ->
    let [before'a, after'a, after'b] = scanl expr' state [a, b]
     in gate'
          Star
          after'b
          (expr'wire before'a a)
          (set'recip True . expr'wire after'a $ b)
  Ebin o a b ->
    let [before'a, after'a, after'b] = scanl expr' state [a, b]
     in gate' o after'b (expr'wire before'a a) (expr'wire after'a b)
  e -> die $ "Error, invalid expr found: " ++ show e
{-# INLINEABLE expr' #-}

-- | If-Convert if-expression into gates:
-- if a then b else c == a*b + (1-a)*c
expr'if :: (Num a) => State a -> Expr -> Expr -> Expr -> State a
expr'if state a b c =
  let out = g'owire . head . fst
      cond'a = expr' state a
      a'mul'b =
        gate'
          Star
          (expr' cond'a b)
          (expr'wire state a)
          (expr'wire cond'a b)
      neg'a = gate' Star a'mul'b (val'const (-1)) (out cond'a)
      neg'a'one = gate' Plus neg'a unit'const (out neg'a)
      neg'a'one'mul'c =
        gate'
          Star
          (expr' neg'a'one c)
          (out neg'a'one)
          (expr'wire neg'a'one c)
   in gate' Plus neg'a'one'mul'c (out a'mul'b) (out neg'a'one'mul'c)
{-# INLINEABLE expr'if #-}

-- | Convert expressions into wires based on the given state
expr'wire :: (Num a) => State a -> Expr -> Wire a
expr'wire state = \case
  Value (N n) -> val'const (fromIntegral n)
  Value (V v) -> unit'var v
  a -> g'owire . head . fst . expr' state $ a
{-# INLINE expr'wire #-}

-- | Construct a gate with given wires and add to the given state
-- This is tail-call where every recursive 'expr' call ends
gate' :: (Num a) => Ops -> State a -> Wire a -> Wire a -> State a
gate' op (gates, wmap) lwire rwire = case op of
  Assign -> (gates, bind'wires wmap lwire rwire)
  _ ->
    let norm wire@Wire {..}
          | out'wirep wire = wire
          | otherwise = set'recip w'recip (wmap ~~> wire)
        prefix'expr =
          set'expr
            (unwords ["(" ++ pretty op, w'expr lwire, w'expr rwire ++ ")"])
     in ( Gate
            (gate'op op)
            (norm lwire)
            (norm rwire)
            (prefix'expr . out'wire $ gates)
            : gates,
          wmap
        )
{-# INLINE gate' #-}

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
out'wire :: (Num a) => [Gate a] -> Wire a
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
bind'wires :: Wmap a -> Wire a -> Wire a -> Wmap a
bind'wires wmap Wire {..} rwire
  | member w'key wmap =
      die . unwords $
        ["Error, found conflicting definition for:", w'key ++ ",", w'expr]
  | otherwise =
      wmap <~ (w'key, rwire)
{-# INLINEABLE bind'wires #-}

-- | Get vector of all wire-keys used in 'circuit':
-- @[const (&1), instances.., witnesses.., auxiliary symbols (~1,~2,..)..]@
-- This is exactly the same as QAP bases
wire'keys :: Circuit a -> [String]
wire'keys Circuit {..} =
  const'key
    : concat [sort c'pubs, sort c'privs, w'key . g'owire <$> c'gates]
{-# INLINE wire'keys #-}

-- | Clean up all of wire exprs in circuit
rm'expr :: Circuit a -> Circuit a
rm'expr circuit@Circuit {..} =
  let rm'expr'wire = set'expr mempty
      rm'expr'gate gate@Gate {..} =
        gate
          { g'lwire = rm'expr'wire g'lwire,
            g'rwire = rm'expr'wire g'rwire,
            g'owire = rm'expr'wire g'owire
          }
   in circuit {c'gates = rm'expr'gate <$> c'gates}
{-# INLINE rm'expr #-}
