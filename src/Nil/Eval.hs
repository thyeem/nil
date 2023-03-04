{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

--------------------------------------------------------------------------------
--- zk-SNARKs circuit evaluator
--------------------------------------------------------------------------------

module Nil.Eval where

import Data.List (foldl')
import Data.Map (keys)
import Data.Maybe (fromJust)
import Nil.Circuit
import Nil.Curve (Curve (..), ap, mulg, p'y)
import Nil.Data (NIL (..), UL (..), nil, nil', unil, unil')
import Nil.Field (Field)
import Nil.Utils (blake2b, bytes'from'int'len, die, int'from'bytes)

{- | Get vector of all wire-values used in 'circuit':
 This is values corresponding to 'wire'keys' and the same as QAP witness vector
-}
wire'vals
  :: (Integral r, Integral q, Field r, Field q)
  => Curve i q
  -> Wmap r
  -> Circuit r
  -> [r]
wire'vals c wmap circuit@Circuit {..} =
  unil
    . w'val
    . (eval'circuit xmap xcirc ~>)
    <$> wire'keys circuit
 where
  xmap = extend'wire c <$> wmap
  xcirc = circuit {c'gates = extend'gate c <$> c'gates}
{-# INLINE wire'vals #-}

-- @statement@ is an circuit evaluation result that a prover can use to prove it
statement
  :: (Integral r, Integral q, Field r, Field q)
  => Curve i q
  -> Wmap r
  -> Circuit r
  -> r
statement c wmap circuit@Circuit {..} =
  unil . w'val $ eval'circuit xmap xcirc ~> return'key
 where
  xmap = extend'wire c <$> wmap
  xcirc = circuit {c'gates = extend'gate c <$> c'gates}
{-# INLINE statement #-}

-- | Evaluate Circuit with a given set of @(x, w)@
eval'circuit
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Circuit (NIL i r q)
  -> Wmap (NIL i r q)
eval'circuit wmap Circuit {..} = foldl' eval'gate wmap c'gates
{-# INLINE eval'circuit #-}

-- | Extends a wire to a NILdata wire
extend'wire :: Curve i q -> Wire r -> Wire (NIL i r q)
extend'wire c w@Wire {..} = w {w'val = nil c w'val}
{-# INLINE extend'wire #-}

-- | Extends all gate wires to NILdata-wire
extend'gate :: Curve i q -> Gate r -> Gate (NIL i r q)
extend'gate c g@Gate {..} =
  g
    { g'lwire = extend'wire c g'lwire
    , g'rwire = extend'wire c g'rwire
    , g'owire = extend'wire c g'owire
    }
{-# INLINE extend'gate #-}

-- | Get the wire bases vector from Wmap
vec'fromWmap :: Num a => Wmap a -> [a]
vec'fromWmap wmap =
  w'val . (wmap ~>)
    <$> filter (/= const'key) (keys wmap)
{-# INLINE vec'fromWmap #-}

-- | Get a Wmap from List in forms of [(String, r)]
wmap'fromList :: Num a => [(String, a)] -> Wmap a
wmap'fromList =
  foldr
    ( \(key, val) wmap ->
        wmap <~ (key, set'val val . unit'var $ key)
    )
    (mempty <~~ unit'const)
{-# INLINE wmap'fromList #-}

-- | Evaluate each gate based on gate operator
eval'gate
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'gate wmap gate@Gate {..} =
  case g'op of
    Mul -> eval (*) wmap gate
    Add -> eval (+) wmap gate
    Mod' -> eval'mod wmap gate
    Exp' -> eval'exp wmap gate
    End -> eval'end wmap gate
    Hash' -> eval'hash wmap gate
    EPx' -> eval'epx wmap gate
    EPy' -> eval'epy wmap gate
    EkG' -> eval'ekg wmap gate
    ECP' -> eval'ecp wmap gate
    _ -> eval'rop wmap gate
{-# INLINEABLE eval'gate #-}

-- | Evaluate a wire with a given Wmap
(~~) :: Fractional a => Wmap a -> Wire a -> a
(~~) wmap wire@Wire {w'key}
  | w'recip wire = recip val
  | otherwise = val
 where
  val
    | const'wirep wire = w'val wire
    | otherwise = w'val wire * w'val (wmap ~> w'key)
{-# INLINE (~~) #-}

-- | Evaluate a wire with a given weight then return the wire
(~~~) :: Num a => a -> Wire a -> Wire a
(~~~) val wire@Wire {w'val} = set'val (val * w'val) wire
{-# INLINE (~~~) #-}

-- | Evaluate gate
eval :: Fractional a => (a -> a -> a) -> Wmap a -> Gate a -> Wmap a
eval op wmap Gate {..} = wmap <~~ (val ~~~ g'owire)
 where
  val = (wmap ~~ g'lwire) `op` (wmap ~~ g'rwire)
{-# INLINEABLE eval #-}

-- | Evaluate only when both wires are scalars
eval'scalar
  :: (Num a, Integral r, Integral q, Field r, Field q)
  => (a -> a -> NIL i r q)
  -> String
  -> Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'scalar op label wmap Gate {..} = wmap <~~ (op lval rval ~~~ g'owire)
 where
  lval = val g'lwire
  rval = val g'rwire
  val wire = case wmap ~~ wire of
    NIL _ (U v) -> fromIntegral v
    _ ->
      die $
        unwords
          ["Error, used", label, "on non-scalar wire:", w'key wire]
{-# INLINEABLE eval'scalar #-}

eval'exp
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'exp wmap g = eval'scalar ((nil c .) . (^)) "(^)" wmap g
 where
  NIL c _ = wmap ~~ g'rwire g
{-# INLINEABLE eval'exp #-}

-- | Evaluate modulo operator
eval'mod
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'mod wmap g = eval'scalar ((nil c .) . mod) "'mod'" wmap g
 where
  NIL c _ = wmap ~~ g'rwire g
{-# INLINEABLE eval'mod #-}

-- | Evaluate the last gate of circuit
eval'end :: Wmap a -> Gate a -> Wmap a
eval'end wmap Gate {..} = (wmap <~~ end) <~~ set'key return'key end
 where
  end = set'key end'key (wmap ~~> g'rwire)
{-# INLINEABLE eval'end #-}

-- | Evaluate hash operator
eval'hash
  :: (Integral r, Field r, Integral q, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'hash wmap Gate {..} = wmap <~~ (hash (wmap ~~ g'rwire) ~~~ g'owire)
 where
  NIL c _ = wmap ~~ g'lwire
  hash =
    nil c
      . fromIntegral
      . int'from'bytes
      . blake2b 32 mempty
      . bytes'from'int'len 32
      . fromIntegral
      . unil
{-# INLINEABLE eval'hash #-}

-- | Evalate gates of relational operators
eval'rop
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'rop wmap Gate {..} = wmap <~~ (val ~~~ g'owire)
 where
  NIL c _ = wmap ~~ g'lwire
  val
    | (wmap ~~ g'lwire) `op` (wmap ~~ g'rwire) = nil c 1
    | otherwise = nil c 0
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
eval'epx
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'epx wmap Gate {..} = wmap <~~ (xval ~~~ g'owire)
 where
  NIL c val = wmap ~~ g'rwire
  xval = case val of
    L _ 0 -> die "Error, used (:) on point at infinity"
    L x _ -> nil c . fromIntegral $ x
    U _ -> die $ "Error, used (:) on non-EC point wire: " ++ w'key g'rwire
{-# INLINEABLE eval'epx #-}

-- | Evaluate operator of getting y-coordinate from elliptic curve points
eval'epy
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'epy wmap Gate {..} = wmap <~~ (yval ~~~ g'owire)
 where
  o@(NIL c val) = wmap ~~ g'rwire
  yval = case val of
    L _ 0 -> die "Error, used (;) on point at infinity"
    L {} -> nil c . fromIntegral . fromJust . p'y . unil' $ o
    U _ -> die $ "Error, used (;) on non-EC point wire: " ++ w'key g'rwire
{-# INLINEABLE eval'epy #-}

-- | [k]G
eval'ekg
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'ekg wmap g =
  eval'scalar @Integer (((nil' c . mulg c) .) . seq) "([])" wmap g
 where
  NIL c _ = wmap ~~ g'rwire g
{-# INLINEABLE eval'ekg #-}

-- | [x,y]
eval'ecp
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'ecp wmap g = eval'scalar ((nil' c .) . ap c) "([,])" wmap g
 where
  NIL c _ = wmap ~~ g'rwire g
{-# INLINEABLE eval'ecp #-}
