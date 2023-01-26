{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}

module Nil.Evaluator where

import Control.DeepSeq (NFData)
import Data.ByteString (append)
import Data.List (foldl')
import Nil.Base (sqrt'zpz)
import Nil.Circuit
  ( Circuit (..)
  , Gate (..)
  , Gateop (..)
  , Table
  , Wire (..)
  , const'wirep
  , ext'wirep
  , set'expr
  , set'flag
  , set'key
  , set'unit'key
  , set'unit'val
  , set'val
  , unit'wire
  , wire'keys
  , (!)
  , (!~)
  , (<~)
  )
import Nil.Curve
  ( Curve (..)
  , Point (..)
  , ap
  , mulg
  , toA
  , (.*)
  )
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

--------------------------------------------------------------------------------
--- [zkp] zk-SNARKs circuit evaluator
--------------------------------------------------------------------------------

{- | Get vector of all wire-values used in 'circuit':
 This is values corresponding to 'wire'keys' and the same as QAP witness vector
-}
wire'vals
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Circuit f
  -> [f]
wire'vals curve table circuit =
  (eval'circuit curve table circuit !) <$> wire'keys circuit
{-# INLINE wire'vals #-}

-- @statement@ is an circuit evaluation result that a prover can use to prove it
statement
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Circuit f
  -> f
statement curve table circuit =
  eval'circuit curve table circuit ! "return"
{-# INLINE statement #-}

-- | Evaluate Circuit with a given set of @(x, w)@
eval'circuit
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Circuit f
  -> Table f
eval'circuit curve table Circuit {..} =
  foldl' (eval'gate curve) table c'gates <~ unit'wire
{-# INLINE eval'circuit #-}

-- | Evaluate each gate based on gate operator
eval'gate
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Gate f
  -> Table f
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
(=~) :: Fractional f => Table f -> Wire f -> f
(=~) table wire@Wire {..} =
  let val
        | const'wirep wire = w'val
        | otherwise = w'val * (table ! w'key)
   in if
          | w'flag == 1 -> recip val
          | w'flag == 0 -> val
          | otherwise ->
              die . unwords $
                ["Error, illegal wire to evaluate:", w'key ++ ",", w'expr]
{-# INLINE (=~) #-}

-- | Check if both gate input wires are extended wires
and'ext'wirep :: Integral f => Table f -> Gate f -> Bool
and'ext'wirep table Gate {..} =
  ext'wirep (table !~ g'lwire) && ext'wirep (table !~ g'rwire)
{-# INLINEABLE and'ext'wirep #-}

-- | Check if one of gate input wires is an extended wire
xor'ext'wirep :: Integral f => Table f -> Gate f -> Bool
xor'ext'wirep table Gate {..} = (left && not right) || (not left && right)
 where
  left = ext'wirep $ table !~ g'lwire
  right = ext'wirep $ table !~ g'rwire
{-# INLINEABLE xor'ext'wirep #-}

-- | Check if none of gate input wires is an extended wire
nor'ext'wirep :: Integral f => Table f -> Gate f -> Bool
nor'ext'wirep table Gate {..} =
  not $ ext'wirep (table !~ g'lwire) || ext'wirep (table !~ g'rwire)
{-# INLINEABLE nor'ext'wirep #-}

-- | Evaluate gate when both gate input wires are extended
eval'and'ext'wire
  :: (Integral f, Eq k, Integral k, Fractional k, Field k)
  => Curve k
  -> (Point k -> Point k -> Point k)
  -> Table f
  -> Gate f
  -> Table f
eval'and'ext'wire curve op table Gate {..} =
  let wire =
        wire'from'p $
          p'from'wire curve (table !~ g'lwire)
            `op` p'from'wire curve (table !~ g'rwire)
   in table <~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'and'ext'wire #-}

-- | Evaluate gate when one of gate input wires is an extended
eval'xor'ext'wire
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k)
  => Curve k
  -> (Point k -> f -> Point k)
  -> Table f
  -> Gate f
  -> Table f
eval'xor'ext'wire curve op table Gate {..} =
  let wire
        | ext'wirep (table !~ g'lwire) =
            wire'from'p $
              p'from'wire curve (table !~ g'lwire) `op` (table =~ g'rwire)
        | otherwise =
            wire'from'p $
              p'from'wire curve (table !~ g'rwire) `op` (table =~ g'lwire)
   in table <~ set'key (w'key g'owire) wire
{-# INLINEABLE eval'xor'ext'wire #-}

-- | Evaluate gate when both gate input wires are scalar wires (no extended wires)
eval'nor'ext'wire
  :: (Integral f, Fractional f) => (f -> f -> f) -> Table f -> Gate f -> Table f
eval'nor'ext'wire op table Gate {..} =
  let wire = set'val (table =~ g'lwire `op` (table =~ g'rwire)) g'owire
   in table <~ set'key (w'key g'owire) wire
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
eval'end :: (Integral f, Fractional f) => Table f -> Gate f -> Table f
eval'end table Gate {..} =
  let val = table =~ g'rwire
   in (table <~ set'val (val * val) g'owire)
        <~ set'val val (set'unit'key "return")
{-# INLINEABLE eval'end #-}

-- | Evaluate gate of @Mul (*)@ base gate operator
eval'mul
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Gate f
  -> Table f
eval'mul curve table g
  | and'ext'wirep table g = err'operands g "(*)"
  | xor'ext'wirep table g = eval'xor'ext'wire curve (.*) table g
  | otherwise = eval'nor'ext'wire (*) table g
{-# INLINEABLE eval'mul #-}

-- | Evaluate gate of @Add (+)@ base gate operator
eval'add
  :: (Integral f, Fractional f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Gate f
  -> Table f
eval'add curve table g
  | and'ext'wirep table g = eval'and'ext'wire curve (+) table g
  | xor'ext'wirep table g = err'operands g "(+)"
  | otherwise = eval'nor'ext'wire (+) table g
{-# INLINEABLE eval'add #-}

-- | Evaluate exponentiation
eval'exp :: (Integral f, Fractional f) => Table f -> Gate f -> Table f
eval'exp table g
  | nor'ext'wirep table g = eval'nor'ext'wire (^) table g
  | otherwise = err'operands g "(^)"
{-# INLINEABLE eval'exp #-}

-- | Evaluate modulo operator
eval'mod :: (Integral f, Fractional f) => Table f -> Gate f -> Table f
eval'mod table g
  | nor'ext'wirep table g = eval'nor'ext'wire mod table g
  | otherwise = err'operands g "mod"
{-# INLINEABLE eval'mod #-}

-- | Evaluate hash operator
eval'hash :: (Integral f, Fractional f) => Table f -> Gate f -> Table f
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
  => Table f
  -> Gate f
  -> Table f
eval'rop table g@Gate {..}
  | nor'ext'wirep table g =
      let wire =
            if (table =~ g'lwire) `op` (table =~ g'rwire)
              then unit'wire
              else set'unit'val 0
       in table <~ set'key (w'key g'owire) wire
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
eval'x'from'p :: Integral f => Table f -> Gate f -> Table f
eval'x'from'p table g@Gate {..}
  | xor'ext'wirep table g =
      let wire =
            set'unit'val
              . fromIntegral
              . w'val
              $ table !~ g'rwire
       in table <~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "(:)"
{-# INLINEABLE eval'x'from'p #-}

-- | Evaluate operator of getting y-coordinate from elliptic curve points
eval'y'from'p
  :: (Integral f, Integral k) => Curve k -> Table f -> Gate f -> Table f
eval'y'from'p curve table g@Gate {..}
  | xor'ext'wirep table g =
      let wire =
            set'unit'val
              . fromIntegral
              . y'from'wire curve
              $ table !~ g'rwire
       in table <~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "(;)"
{-# INLINEABLE eval'y'from'p #-}

eval'ekG
  :: (Integral f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Gate f
  -> Table f
eval'ekG curve table g@Gate {..}
  | nor'ext'wirep table g =
      let wire =
            wire'from'p
              . mulg curve
              . w'val
              $ table !~ g'rwire
       in table <~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "[k]"
{-# INLINEABLE eval'ekG #-}

eval'exy
  :: (Integral f, Integral k, Fractional k, Field k, NFData k)
  => Curve k
  -> Table f
  -> Gate f
  -> Table f
eval'exy curve table g@Gate {..}
  | nor'ext'wirep table g =
      let wire =
            wire'from'p $
              ap
                curve
                (fromIntegral . w'val $ table !~ g'lwire)
                (fromIntegral . w'val $ table !~ g'rwire)
       in table <~ set'key (w'key g'owire) wire
  | otherwise = err'operands g "[x,y]"
{-# INLINEABLE eval'exy #-}

-- | Clean up all of wire exprs in circuit
clean'circuit :: Circuit f -> Circuit f
clean'circuit circuit@Circuit {..} =
  let clean'wire = set'expr mempty
      clean'gate gate@Gate {..} =
        gate
          { g'lwire = clean'wire g'lwire
          , g'rwire = clean'wire g'rwire
          , g'owire = clean'wire g'owire
          }
   in circuit {c'gates = clean'gate <$> c'gates}
{-# INLINE clean'circuit #-}

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
--- [mpc] zksign evaluator: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

{- | Homomorphically ecrypt secrets based on a circuit and a random field generator.
 Partially evaluate Circuit with @Priv@ secret value -> 'Signed Circuit'.
-}
sign'circuit
  :: (Integral f, Fractional f) => Circuit f -> Table f -> Circuit f
sign'circuit = undefined

-- sign'circuit circuit@Circuit {..} secrets g = circuit
-- { c'gates = [ valid'sign'gate c'witness $ signGate gate secrets g

{- | gate <- c'gates
 ]
 }
 where g = fromIntegral . (=| fromInteger gamma) . fst . unEF $ eG1G2
-}

{- | Signing each gate by partially evaluating with secrets and a field generator
 signGate :: (Integral f, Fractional f) => Gate f -> Table f -> f -> Gate f
 signGate gate@Gate {..} secrets g = case g'op of
 Mul -> gate { g'op    = Exp'
 , g'lwire = signWire g'lwire secrets g
 , g'rwire = signWire g'rwire secrets g
 }
 Add -> gate { g'op    = Mul
 , g'lwire = signWire g'lwire secrets g
 , g'rwire = signWire g'rwire secrets g
 }
 Exp' -> gate { g'op    = Exp'
 , g'lwire = signWire g'lwire secrets 1
 , g'rwire = signWire g'rwire secrets 1
 }
 gop -> die $ "Not allowed Gate operator: " <> show gop
-}

{- | Signing each wire by partially evaluating with secrets and a field generator
 signWire :: (Integral f, Fractional f) => Wire f -> Table f -> f -> Wire f
 signWire w@Wire {..} secrets g
 | M.member w'key secrets = Wire { w'key    = const'key
 , w'val    = finish (secrets ! w'key)
 , w'flag = 0
 }
 | otherwise = w
 where
 finish val | g == 1             = val
 | g /= 1 && val == 0 = g
 | otherwise          = g ^ val
-}

{- | Validate a hased circuit
 valid'sign'gate
 :: (Integral f, Fractional f) => Table (Wire f) -> Gate f -> Gate f
 valid'sign'gate filter' gate@Gate { g'lwire, g'rwire }
 | M.member (w'key g'lwire) filter'
 = die $ "Error, not assigned secret variable: " ++ w'key g'lwire
 | M.member (w'key g'rwire) filter'
 = die $ "Error, not assigned secret variable: " ++ w'key g'rwire
 | otherwise
 = gate
-}

--------------------------------------------------------------------------------
