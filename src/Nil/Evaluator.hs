{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Nil.Evaluator where

import Control.DeepSeq (NFData)
import Data.ByteString (append)
import Data.List (foldl', nub, sortOn)
import Data.Map (Map, assocs, elems, keys, member)
import Nil.Base (sqrt'zpz)
import Nil.Circuit
  ( Circuit (..)
  , Gate (..)
  , Gateop (..)
  , W'table
  , Wire (..)
  , and'ext'wirep
  , const'wirep
  , either'by
  , ext'wirep
  , nor'ext'wirep
  , out'prefix
  , out'wirep
  , set'expr
  , set'flag
  , set'key
  , set'unit'key
  , set'unit'val
  , set'val
  , unit'wire
  , wire'keys
  , xor'
  , xor'ext'wirep
  , (<~)
  , (<~~)
  , (~>)
  , (~~>)
  )
import Nil.Curve
  ( Curve (..)
  , Point (..)
  , ap
  , mulg
  , toA
  , (.*)
  )
import Nil.Ecdata (G1, G2)
import Nil.Field (Field)
import Nil.Reorg (O'table, amp'wirep, gen'otable)
import Nil.Utils
  ( blake2b
  , bytes'from'int'len
  , bytes'from'str
  , die
  , hex'from'bytes
  , int'from'bytes
  , sha256
  )

--------------------------------------------------------------------------------
--- [zkp] zk-SNARKs circuit evaluator
--------------------------------------------------------------------------------

{- | Get vector of all wire-values used in 'circuit':
 This is values corresponding to 'wire'keys' and the same as QAP witness vector
-}
wire'vals
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Circuit f
  -> [f]
wire'vals curve table circuit =
  w'val . (eval'circuit curve table circuit ~>) <$> wire'keys circuit
{-# INLINE wire'vals #-}

-- @statement@ is an circuit evaluation result that a prover can use to prove it
statement
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Circuit f
  -> f
statement curve table circuit =
  w'val $ eval'circuit curve table circuit ~> "return"
{-# INLINE statement #-}

-- | Evaluate Circuit with a given set of @(x, w)@
eval'circuit
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Circuit f
  -> W'table f
eval'circuit curve table Circuit {..} =
  foldl' (eval'gate curve) table c'gates <~~ unit'wire
{-# INLINE eval'circuit #-}

-- | Evaluate each gate based on gate operator
eval'gate
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Gate f
  -> W'table f
eval'gate curve table gate@Gate {..} =
  case g'op of
    End -> eval'end table gate
    Mul -> eval'mul curve table gate
    Add -> eval'add curve table gate
    Mod' -> eval'mod table gate
    Exp' -> eval'exp table gate
    Hash' -> eval'hash table gate
    Px' -> eval'x'from'p table gate
    Py' -> eval'y'from'p curve table gate
    EkG' -> eval'ekG curve table gate
    Exy' -> eval'exy curve table gate
    _ -> eval'rop table gate
{-# INLINEABLE eval'gate #-}

-- | Get the wire unlifted by evaluating by key
(~~~>) :: Fractional f => W'table f -> Wire f -> f
(~~~>) table wire@Wire {w'key, w'flag, w'expr} =
  let val
        | const'wirep wire = w'val wire
        | otherwise = w'val wire * w'val (table ~> w'key)
   in if
          | w'flag == 1 -> recip val
          | w'flag == 0 -> val
          | otherwise ->
              die . unwords $
                ["Error, illegal wire to evaluate:", w'key ++ ",", w'expr]
{-# INLINE (~~~>) #-}

-- | Evaluate gate when both gate input wires are extended
eval'and'ext'wire
  :: (Integral f, Eq k, Integral k, Fractional k, Field k)
  => Curve k
  -> (Point k -> Point k -> Point k)
  -> W'table f
  -> Gate f
  -> W'table f
eval'and'ext'wire curve op table Gate {..} =
  let wire =
        wire'from'p $
          p'from'wire curve (table ~~> g'lwire)
            `op` p'from'wire curve (table ~~> g'rwire)
   in table <~~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'and'ext'wire #-}

-- | Evaluate gate when one of gate input wires is an extended
eval'xor'ext'wire
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k)
  => Curve k
  -> (Point k -> f -> Point k)
  -> W'table f
  -> Gate f
  -> W'table f
eval'xor'ext'wire curve op table g@Gate {..} =
  let (ext, scalar) = either'by (ext'wirep . (table ~~>)) g
      wire =
        wire'from'p $
          p'from'wire curve (table ~~> ext)
            `op` (table ~~~> scalar)
   in table <~~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'xor'ext'wire #-}

-- | Evaluate gate when both gate input wires are scalar wires (no extended wires)
eval'nor'ext'wire
  :: (Integral f, Fractional f) => (f -> f -> f) -> W'table f -> Gate f -> W'table f
eval'nor'ext'wire op table Gate {..} =
  let wire = set'val (table ~~~> g'lwire `op` (table ~~~> g'rwire)) g'owire
   in table <~~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'nor'ext'wire #-}

-- | Get an elliptic curve point on a given wire
p'from'wire
  :: (Integral f, Eq k, Integral k, Fractional k, Field k)
  => Curve k
  -> Wire f
  -> Point k
p'from'wire curve wire =
  ap
    curve
    (fromIntegral . w'val $ wire)
    (y'from'wire curve wire)
{-# INLINE p'from'wire #-}

-- | Get y-coordinate from a given point-wire
y'from'wire :: (Integral f, Integral k) => Curve k -> Wire f -> k
y'from'wire curve Wire {..} =
  let sqrt'y2 =
        sqrt'zpz
          (toInteger $ (x * x + c'a curve) * x + c'b curve)
          (c'p curve)
      x = fromIntegral w'val
      y = case sqrt'y2 of
        Just a -> a
        _ ->
          die . unwords $
            ["Error, wire-point is not on curve", w'key ++ ",", w'expr]
   in if
          | w'flag == 0 -> die "Error, not an elliptic point"
          | even w'flag -> fromIntegral y
          | otherwise -> fromIntegral (negate y)
{-# INLINE y'from'wire #-}

wire'from'p
  :: (Integral f, Eq k, Integral k, Fractional k, Field k)
  => Point k
  -> Wire f
wire'from'p point = case toA point of
  A _ x y ->
    let wire = set'unit'val (fromIntegral x)
     in if even y then set'flag 2 wire else set'flag 3 wire
  _ -> die "Error, cannot convert point at infinity into wire"
{-# INLINE wire'from'p #-}

-- | Error when evaluating gate with an illegal operator and operands (wires)
err'operands :: Gate f -> String -> a
err'operands Gate {..} sym =
  die . unwords $
    [ "Error, not allowed " ++ sym ++ " operator between:"
    , w'key g'lwire
    , "and"
    , w'key g'rwire
    ]

-- | Evaluate the last gate of circuit
eval'end :: (Integral f, Fractional f) => W'table f -> Gate f -> W'table f
eval'end table Gate {..} =
  let val = table ~~~> g'rwire
   in (table <~~ set'val (val * val) g'owire)
        <~~ set'val val (set'unit'key "return")
{-# INLINEABLE eval'end #-}

-- | Evaluate gate of @Mul (*)@ base gate operator
eval'mul
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Gate f
  -> W'table f
eval'mul curve table g
  | and'ext'wirep table g = err'operands g "(*)"
  | xor'ext'wirep table g = eval'xor'ext'wire curve (.*) table g
  | otherwise = eval'nor'ext'wire (*) table g
{-# INLINEABLE eval'mul #-}

-- | Evaluate gate of @Add (+)@ base gate operator
eval'add
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Gate f
  -> W'table f
eval'add curve table g
  | and'ext'wirep table g = eval'and'ext'wire curve (+) table g
  | xor'ext'wirep table g = err'operands g "(+)"
  | otherwise = eval'nor'ext'wire (+) table g
{-# INLINEABLE eval'add #-}

-- | Evaluate exponentiation
eval'exp :: (Integral f, Fractional f) => W'table f -> Gate f -> W'table f
eval'exp table g
  | nor'ext'wirep table g = eval'nor'ext'wire (^) table g
  | otherwise = err'operands g "(^)"
{-# INLINEABLE eval'exp #-}

-- | Evaluate modulo operator
eval'mod :: (Integral f, Fractional f) => W'table f -> Gate f -> W'table f
eval'mod table g
  | nor'ext'wirep table g = eval'nor'ext'wire mod table g
  | otherwise = err'operands g "mod"
{-# INLINEABLE eval'mod #-}

-- | Evaluate hash operator
eval'hash :: (Integral f, Fractional f) => W'table f -> Gate f -> W'table f
eval'hash table g
  | nor'ext'wirep table g =
      let hash =
            fromIntegral
              . int'from'bytes
              . blake2b 32 mempty
              . bytes'from'int'len 32
              . fromIntegral
       in eval'nor'ext'wire (const hash) table g
  | otherwise = err'operands g "hash"
{-# INLINEABLE eval'hash #-}

-- | Evalate gates of relational operators
eval'rop
  :: (Eq f, Ord f, Integral f, Fractional f)
  => W'table f
  -> Gate f
  -> W'table f
eval'rop table g@Gate {..}
  | nor'ext'wirep table g =
      let wire =
            if (table ~~~> g'lwire) `op` (table ~~~> g'rwire)
              then unit'wire
              else set'unit'val 0
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "relational"
 where
  op = case g'op of
    GT' -> (>)
    LT' -> (<)
    GE' -> (>=)
    LE' -> (<=)
    EQ' -> (==)
    NE' -> (/=)
    _ -> die $ "Error, no such operator: " ++ show g'op
{-# INLINEABLE eval'rop #-}

-- | Evaluate operator of getting x-coordinate from elliptic curve points
eval'x'from'p :: Integral f => W'table f -> Gate f -> W'table f
eval'x'from'p table g@Gate {..}
  | xor'ext'wirep table g =
      let wire = set'unit'val . fromIntegral . w'val $ table ~~> g'rwire
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "(:)"
{-# INLINEABLE eval'x'from'p #-}

-- | Evaluate operator of getting y-coordinate from elliptic curve points
eval'y'from'p
  :: (Integral f, Integral k) => Curve k -> W'table f -> Gate f -> W'table f
eval'y'from'p curve table g@Gate {..}
  | xor'ext'wirep table g =
      let wire =
            set'unit'val . fromIntegral . y'from'wire curve $
              table ~~> g'rwire
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "(;)"
{-# INLINEABLE eval'y'from'p #-}

eval'ekG
  :: (Integral f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Gate f
  -> W'table f
eval'ekG curve table g@Gate {..}
  | nor'ext'wirep table g =
      let wire = wire'from'p . mulg curve . w'val $ table ~~> g'rwire
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "[k]"
{-# INLINEABLE eval'ekG #-}

eval'exy
  :: (Integral f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> W'table f
  -> Gate f
  -> W'table f
eval'exy curve table g@Gate {..}
  | nor'ext'wirep table g =
      let wire =
            wire'from'p $
              ap
                curve
                (fromIntegral . w'val $ table ~~> g'lwire)
                (fromIntegral . w'val $ table ~~> g'rwire)
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "[x,y]"
{-# INLINEABLE eval'exy #-}

-- | Clean up all of wire exprs in circuit
rm'expr :: Circuit f -> Circuit f
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

-- | Get a hash value from a given circuit
hash'circuit :: String -> Circuit f -> String
hash'circuit salt Circuit {..} =
  let from'str = sha256 . bytes'from'str
      from'ba = foldl1 ((sha256 .) . append)
      hash'wire Wire {..} = from'str (w'key ++ salt)
      hash'gate Gate {..} =
        case g'op of
          Add -> from'ba $ hash'wire <$> [g'lwire, g'rwire, g'owire]
          Mul -> from'ba $ hash'wire <$> [g'rwire, g'lwire, g'owire]
          _ -> from'ba $ hash'wire <$> [g'owire, g'lwire, g'rwire]
   in hex'from'bytes . from'ba $ hash'gate <$> c'gates

--------------------------------------------------------------------------------
--- [mpc] nil-sign evaluator: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

-- | Multiple-signature object for nil-sign
data NilSig f = NilSig
  { n'keys :: (Point G1, Point G2)
  , n'hash :: String
  , n'sig :: Circuit f
  }
  deriving (Eq, Show)

-- | Lookup table describing a circuit as DAG
type G'table f = Map String [Gate f]

{- | Put an edge record to the graph-table
 key -> out-wire of [FROM gate]
 gate -> [TO gate]
-}
(<<~) :: Eq f => G'table f -> (String, Gate f) -> G'table f
(<<~) table (key, gate)
  | member key table =
      let gates = table ~> key
       in table <~ (key, nub $ gate : gates)
  | otherwise = table <~ (key, [gate])
{-# INLINE (<<~) #-}

-- | Initialize nil-signature
init'sig :: Circuit f -> NilSig f
init'sig = NilSig (O, O) mempty
{-# INLINE init'sig #-}

{- | Homomorphically ecrypt secrets based on a reorged circuit.
 @Sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets
-}
sign'sig
  :: (Integral f, Fractional f) => NilSig f -> W'table f -> IO (NilSig f)
sign'sig NilSig {..} table = undefined
{-# INLINE sign'sig #-}

gen'gtable :: Eq f => O'table f -> G'table f
gen'gtable o'tab =
  let gates = fst <$> sortOn (negate . snd) (elems o'tab)
      go'wire gate g'tab wire
        | out'wirep wire = g'tab <<~ (w'key wire, gate)
        | otherwise = g'tab
      update g'tab gate@Gate {..} =
        foldl' (go'wire gate) g'tab [g'lwire, g'rwire]
   in foldl' update mempty gates
{-# INLINEABLE gen'gtable #-}

-- | Find the amplifier-knot gate related to the given gate
find'paired'amp :: G'table f -> Gate f -> Gate f
find'paired'amp = undefined

-- | Find the shift-knot gate related to the given gate
find'paired'shift :: G'table f -> Gate f -> Gate f
find'paired'shift = undefined

-- | Get a list of keys of amplifier gates
get'amp'keys :: O'table f -> [String]
get'amp'keys table = foldl' get [] (assocs table)
 where
  get keys (key, (gate, _))
    | xor' amp'wirep gate = key : keys
    | otherwise = keys

-- | Overwrite/replace previous gate with the new evaluated one
(<~!) :: Eq f => O'table f -> (String, Gate f) -> O'table f
(<~!) table (key, gate)
  | member key table =
      let (_, height) = table ~> key
       in table <~ (key, (gate, height))
  | otherwise = die $ "Error, not found gate-key: " ++ key
