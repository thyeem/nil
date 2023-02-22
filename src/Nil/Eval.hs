{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

--------------------------------------------------------------------------------
--- zk-SNARKs circuit evaluator
--------------------------------------------------------------------------------

module Nil.Eval where

import Control.DeepSeq (NFData)
import Data.List (foldl')
import Data.Map (elems, keys)
import Data.Maybe (fromJust, fromMaybe)
import Nil.Base (sqrt'zpz)
import Nil.Circuit
import Nil.Curve (Curve (..), Point (..), ap, mulg, p'x, p'y, toA, (~*))
import Nil.Data (NIL (..), UL (..), nil, unil, unlift)
import Nil.Field (Field)
import Nil.Utils (blake2b, bytes'from'int'len, die, int'from'bytes)

lifted'wirep :: Wire (NIL i r q) -> Bool
lifted'wirep wire = case w'val wire of
  NIL _ (U _) -> False
  _ -> True

-- | Extends a wire to a NIL-type wire
extend'wire :: Curve i q -> Wire r -> Wire (NIL i r q)
extend'wire c w@Wire {..} = w {w'val = nil c w'val}
{-# INLINE extend'wire #-}

-- | Extends all wires from a circuit to NIL-type wires
extend'circuit :: Curve i q -> Circuit r -> Circuit (NIL i r q)
extend'circuit c circuit@Circuit {..} =
  circuit
    { c'gates =
        ( \g@Gate {..} ->
            g
              { g'lwire = extend'wire c g'lwire
              , g'rwire = extend'wire c g'rwire
              , g'owire = extend'wire c g'owire
              }
        )
          <$> c'gates
    }
{-# INLINE extend'circuit #-}

-- | Get the wire bases vector from Wmap
v'fromWmap :: Num r => Wmap r -> [r]
v'fromWmap wmap =
  w'val . (wmap ~>)
    <$> filter (/= const'key) (keys wmap)
{-# INLINE v'fromWmap #-}

-- | Get a Wmap from List in forms of [(String, r)]
wmap'fromList :: Num r => [(String, r)] -> Wmap r
wmap'fromList =
  foldr
    ( \(key, val) wmap ->
        wmap <~ (key, set'val val . unit'var $ key)
    )
    (mempty <~~ unit'const)
{-# INLINE wmap'fromList #-}

{- | Get vector of all wire-values used in 'circuit':
 This is values corresponding to 'wire'keys' and the same as QAP witness vector
-}
wire'vals
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Circuit (NIL i r q)
  -> [r]
wire'vals wmap circuit =
  unil
    . w'val
    . (eval'circuit wmap circuit ~>)
    <$> wire'keys circuit
{-# INLINE wire'vals #-}

-- @statement@ is an circuit evaluation result that a prover can use to prove it
statement
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Circuit (NIL i r q)
  -> r
statement wmap circuit =
  unil . w'val $ eval'circuit wmap circuit ~> return'key
{-# INLINE statement #-}

-- | Evaluate Circuit with a given set of @(x, w)@
eval'circuit
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Circuit (NIL i r q)
  -> Wmap (NIL i r q)
eval'circuit wmap Circuit {..} = foldl' eval'gate wmap c'gates
{-# INLINE eval'circuit #-}

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

-- | Evaluate a NIL-wire with a given wmap
(~~)
  :: (Integral r, Field r, Integral q, Field q)
  => Wmap (NIL i r q)
  -> Wire (NIL i r q)
  -> NIL i r q
(~~) wmap wire@Wire {w'key, w'expr} =
  let val
        | const'wirep wire = w'val wire
        | otherwise = w'val wire * w'val (wmap ~> w'key)
   in if w'recip wire then recip val else val
{-# INLINE (~~) #-}

-- | Evaluate gate
eval
  :: (Integral r, Integral q, Field r, Field q)
  => (NIL i r q -> NIL i r q -> NIL i r q)
  -> Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval op wmap Gate {..} =
  let val = (wmap ~~ g'lwire) `op` (wmap ~~ g'rwire)
   in wmap <~~ set'val val g'owire
{-# INLINEABLE eval #-}

-- | Evaluate only when both wires are scalars
eval'scalar
  :: (Num a, Integral r, Integral q, Field r, Field q)
  => (a -> a -> NIL i r q)
  -> String
  -> Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'scalar op label wmap Gate {..} =
  let val wire = case wmap ~~ wire of
        NIL _ (U v) -> fromIntegral v
        _ ->
          die $
            unwords
              [ "Error, used"
              , label
              , "on non-scalar wire:"
              , w'key wire
              ]
      lval = val g'lwire
      rval = val g'rwire
   in wmap <~~ set'val (op lval rval) g'owire
{-# INLINEABLE eval'scalar #-}

eval'exp
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'exp wmap g =
  let (NIL c _) = wmap ~~ g'rwire g
   in eval'scalar ((nil c .) . (^)) "(^)" wmap g
{-# INLINEABLE eval'exp #-}

-- | Evaluate modulo operator
eval'mod
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'mod wmap g =
  let (NIL c _) = wmap ~~ g'rwire g
   in eval'scalar ((nil c .) . mod) "'mod'" wmap g
{-# INLINEABLE eval'mod #-}

-- | Evaluate the last gate of circuit
eval'end :: Wmap (NIL i r q) -> Gate (NIL i r q) -> Wmap (NIL i r q)
eval'end wmap Gate {..} =
  let end = set'key "~end" (wmap ~~> g'rwire)
   in (wmap <~~ end) <~~ set'key return'key end
{-# INLINEABLE eval'end #-}

-- | Evaluate hash operator
eval'hash
  :: (Integral r, Field r, Integral q, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'hash wmap Gate {..} =
  let (NIL c _) = wmap ~~ g'lwire
      hash =
        nil c
          . fromIntegral
          . int'from'bytes
          . blake2b 32 mempty
          . bytes'from'int'len 32
          . fromIntegral
          . unil
   in wmap <~~ set'val (hash $ wmap ~~ g'rwire) g'owire
{-# INLINEABLE eval'hash #-}

-- | Evalate gates of relational operators
eval'rop
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'rop wmap Gate {..} =
  let (NIL c _) = wmap ~~ g'lwire
      val =
        if (wmap ~~ g'lwire) `op` (wmap ~~ g'rwire)
          then nil c 1
          else nil c 0
   in wmap <~~ set'val val g'owire
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
eval'epx
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'epx wmap Gate {..} =
  let (NIL c val) = wmap ~~ g'rwire
      xval = case val of
        L p -> nil c . fromIntegral . fromJust . p'x $ p
        U _ -> die $ "Error, used (:) on non-EC point wire: " ++ w'key g'rwire
   in wmap <~~ set'val xval g'owire
{-# INLINEABLE eval'epx #-}

-- | Evaluate operator of getting y-coordinate from elliptic curve points
eval'epy
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'epy wmap Gate {..} =
  let (NIL c val) = wmap ~~ g'rwire
      yval = case val of
        L p -> nil c . fromIntegral . fromJust . p'y $ p
        U _ -> die $ "Error, used (;) on non-EC point wire: " ++ w'key g'rwire
   in wmap <~~ set'val yval g'owire
{-# INLINEABLE eval'epy #-}

-- | [k]G
eval'ekg
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'ekg wmap Gate {..} =
  let (NIL c val) = wmap ~~ g'rwire
      kg = case val of
        U v -> NIL c . L . mulg c $ v
        L _ -> die $ "Error, used ([]) on non-scalar wire: " ++ w'key g'rwire
   in wmap <~~ set'val kg g'owire
{-# INLINEABLE eval'ekg #-}

-- | [x,y]
eval'ecp
  :: (Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gate (NIL i r q)
  -> Wmap (NIL i r q)
eval'ecp wmap g =
  let (NIL c _) = wmap ~~ g'rwire g
   in eval'scalar (((NIL c . L) .) . ap c) "([])" wmap g
{-# INLINEABLE eval'ecp #-}
