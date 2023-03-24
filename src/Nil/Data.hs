{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

module Nil.Data
  ( nil,
    unil,
    nil',
    unil',
    NIL (..),
    UL (..),
    lift,
    unlift,
    p'from'ul,
    ul'from'p,
  )
where

import Control.DeepSeq (NFData)
import Data.Maybe (fromMaybe)
import Data.Store (Store)
import GHC.Generics (Generic)
import Nil.Curve (Curve, Point (..), ap, c'g, toA, y'from'x, (~*))
import Nil.Ecdata (BN254, Fr, G1)
import Nil.Field (Field)
import Nil.Utils (Pretty (..), die)

data NIL i r q = NIL (Curve i q) (UL r q)
  deriving (Eq, Show, Generic, NFData)

data UL r q
  = U r -- Unlifted value
  | L q Int -- Lifted value
  deriving (Eq, Show, Generic, NFData)

instance
  (Integral r, Field r, Integral q, Field q) =>
  Num (NIL i r q)
  where
  (+) = add
  {-# INLINE (+) #-}

  (-) = sub
  {-# INLINE (-) #-}

  (*) = mul
  {-# INLINE (*) #-}

  negate = negate'
  {-# INLINE negate #-}

  fromInteger = undefined
  signum = undefined
  abs = undefined

instance
  (Integral r, Field r, Integral q, Field q) =>
  Fractional (NIL i r q)
  where
  recip = recip'
  {-# INLINE recip #-}

  (/) !a !b = a * recip b
  {-# INLINE (/) #-}

  fromRational = undefined

instance
  (Eq r, Ord r, Integral r, Integral q, Field q) =>
  Ord (NIL i r q)
  where
  a <= b = unil a <= unil b

deriving instance Store (UL Fr G1)

deriving instance Store (NIL BN254 Fr G1)

-- | Encode NIL object from scalar
nil :: Curve i q -> r -> NIL i r q
nil c = NIL c . U
{-# INLINE nil #-}

-- | Encode NIL object from EC point
nil' ::
  (Integral q, Field q, Field q) =>
  Curve i q ->
  Point i q ->
  NIL i r q
nil' c = NIL c . ul'from'p
{-# INLINE nil' #-}

-- | Decode NIL object to scalar
unil :: (Integral r, Integral q, Field q) => NIL i r q -> r
unil o = case unlift o of
  NIL _ (U a) -> a
  _ -> die "Error, failed to unload from NIL-object"
{-# INLINE unil #-}

-- | Decode NIL object to EC point
unil' :: (Integral q, Integral q, Field q) => NIL i r q -> Point i q
unil' (NIL c val) = p'from'ul c val
{-# INLINE unil' #-}

-- | lift
lift :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q
lift o@(NIL c val) = case val of
  U a -> nil' c $ c'g c ~* a
  _ -> o
{-# INLINE lift #-}

-- | unlift
unlift :: (Integral r, Integral q, Field q) => NIL i r q -> NIL i r q
unlift o@(NIL c val) = case val of
  L _ 0 -> nil c 0
  L a _ -> nil c . fromIntegral $ a
  _ -> o
{-# INLINE unlift #-}

-- | Encode EC point to NILdata
ul'from'p :: (Integral q, Field q) => Point i q -> UL r q
ul'from'p = \case
  O -> L 0 0
  A _ x y -> L x (if even y then 2 else 3)
  a -> ul'from'p (toA a)
{-# INLINE ul'from'p #-}

-- | Decode EC point from NILdata
p'from'ul :: (Integral q, Field q) => Curve i q -> UL r q -> Point i q
p'from'ul c = \case
  L _ 0 -> O
  L x parity ->
    let y =
          (if odd parity then fst else snd)
            . fromMaybe (die "Error, failed to decode from NILdata")
            $ y'from'x c x
     in ap c x y
  _ -> die "Error, cannot construct EC point from the unlifted"
{-# INLINE p'from'ul #-}

-- | add
add :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q -> NIL i r q
add a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> nil c (x + y)
  (L {}, L {}) -> nil' c (unil' a + unil' b)
  _ -> add (lift a) (lift b)
{-# INLINE add #-}

-- | sub
sub :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q -> NIL i r q
sub a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> nil c (x - y)
  (L {}, L {}) -> nil' c (unil' a - unil' b)
  _ -> sub (lift a) (lift b)
{-# INLINE sub #-}

-- | mul
mul :: (Integral r, Field q, Integral q, Show r) => NIL i r q -> NIL i r q -> NIL i r q
mul a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> nil c (x * y)
  (U x, L {}) -> nil' c (unil' b ~* x)
  (L {}, U y) -> nil' c (unil' a ~* y)
  _ ->
    die . unlines $
      ["Error, undefined (*) operation between lifted values", show a, show b]
{-# INLINE mul #-}

-- | negate
negate' :: (Num r, Field q, Integral q) => NIL i r q -> NIL i r q
negate' o@(NIL c val) = case val of
  U a -> nil c (negate a)
  L {} -> nil' c (unil' o)
{-# INLINE negate' #-}

-- | reciprocal
recip' :: (Fractional r, Field q, Show r) => NIL i r q -> NIL i r q
recip' o@(NIL c val) = case val of
  U a -> nil c (recip a)
  _ ->
    die . unlines $
      ["Error, undefined 'recip' operation on a lifted value", show o]
{-# INLINE recip' #-}

instance (Show r, Show q, Pretty q, Field q) => Pretty (UL r q) where
  pretty = \case
    U a -> show a
    L a parity -> show (a, parity)

instance (Show r, Show q, Pretty q, Field q) => Pretty (NIL i r q) where
  pretty (NIL _ val) = pretty val
