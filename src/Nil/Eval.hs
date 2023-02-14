{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

--------------------------------------------------------------------------------
--- zk-SNARKs circuit evaluator
--------------------------------------------------------------------------------

module Nil.Eval where

import Control.DeepSeq (NFData)
import Data.ByteString (append)
import Data.List (foldl')
import Data.Map (Map, null)
import Data.Maybe (fromMaybe)
import Nil.Base (sqrt'zpz)
import Nil.Circuit
import Nil.Curve (Curve (..), Point (..), ap, mulg, toA, (.*))
import Nil.Field (Field)
import Nil.Utils
  ( blake2b
  , bytes'from'int'len
  , bytes'from'str
  , die
  , hex'from'bytes
  , int'from'bytes
  , sha256
  )

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
  foldl' (eval'gate curve) table c'gates <~~ unit'const
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

-- | Fold a wire into a value by evaluating it with a given table and wire flags
(~~) :: Fractional f => W'table f -> Wire f -> f
(~~) table wire@Wire {w'key, w'expr} =
  let val
        | Data.Map.null table = w'val wire
        | const'wirep wire = w'val wire
        | otherwise = w'val wire * w'val (table ~> w'key)
   in if
          | base'wirep wire -> val
          | recip'wirep wire -> recip val
          | ext'wirep wire -> val -- return x-cooord
          | otherwise ->
              die . unwords $
                ["Error, cannot reduce to a value:", w'key ++ ",", w'expr]
{-# INLINE (~~) #-}

-- | Get an elliptic curve point on a given wire
p'from'wire
  :: (Integral f, Fractional f, Eq k, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Wire f
  -> Point k
p'from'wire curve wire@Wire {..}
  | base'wirep wire || recip'wirep wire = mulg curve (mempty ~~ wire) -- [k]G
  | ext'wirep wire =
      ap
        curve
        (fromIntegral w'val)
        (y'from'wire curve wire)
  | otherwise = die $ "Error, cannot convert to a EC-point: " ++ w'key
{-# INLINE p'from'wire #-}

-- | Get y-coordinate from a given point-wire
y'from'wire :: (Integral f, Integral k) => Curve k -> Wire f -> k
y'from'wire curve Wire {..} =
  let x = fromIntegral w'val
      find'y =
        sqrt'zpz
          (toInteger $ (x * x + c'a curve) * x + c'b curve)
          (c'p curve)
      y =
        fromMaybe
          ( die . unwords $
              ["Error, wire-point is not on curve", w'key ++ ",", w'expr]
          )
          find'y -- y = sqrt(x*x*x + a*x + b) over field
   in if
          | w'flag == P'even -> fromIntegral y
          | w'flag == P'odd -> fromIntegral (negate y)
          | otherwise -> die $ "Error, unexpected wire: " ++ w'key
{-# INLINE y'from'wire #-}

wire'from'p
  :: (Integral f, Eq k, Integral k, Fractional k, Field k)
  => Point k
  -> Wire f
wire'from'p point = case toA point of
  A _ x y ->
    let wire = val'const (fromIntegral x)
     in if even y then set'flag P'even wire else set'flag P'odd wire
  _ -> die "Error, cannot convert point at infinity into wire"
{-# INLINE wire'from'p #-}

-- | Evaluate gate when both gate input wires are extended
eval'and'ext'wire
  :: (Integral f, Eq k, Integral k, Fractional k, Field k, Fractional f, NFData k)
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
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
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
            `op` (table ~~ scalar)
   in table <~~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'xor'ext'wire #-}

-- | Evaluate gate when both gate input wires are scalar wires (no extended wires)
eval'nor'ext'wire
  :: (Integral f, Fractional f) => (f -> f -> f) -> W'table f -> Gate f -> W'table f
eval'nor'ext'wire op table Gate {..} =
  let val = (table ~~ g'lwire) `op` (table ~~ g'rwire)
      wire = set'val val g'owire
   in table <~~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'nor'ext'wire #-}

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
  let val = table ~~ g'rwire
   in (table <~~ set'val (val * val) g'owire)
        <~~ set'val val (unit'var "return")
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
            if (table ~~ g'lwire) `op` (table ~~ g'rwire)
              then unit'const
              else val'const 0
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
      let wire = val'const . fromIntegral . w'val $ table ~~> g'rwire
       in table <~~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "(:)"
{-# INLINEABLE eval'x'from'p #-}

-- | Evaluate operator of getting y-coordinate from elliptic curve points
eval'y'from'p
  :: (Integral f, Integral k) => Curve k -> W'table f -> Gate f -> W'table f
eval'y'from'p curve table g@Gate {..}
  | xor'ext'wirep table g =
      let wire =
            val'const . fromIntegral . y'from'wire curve $
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
