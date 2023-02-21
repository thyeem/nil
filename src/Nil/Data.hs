{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Nil.Data
  ( nil
  , unil
  , NIL (..)
  , UL (..)
  , lift
  , unlift
  )
where

import Control.DeepSeq (NFData)
import Data.Maybe (fromJust)
import GHC.Generics (Generic)
import Nil.Curve (Curve, Point (O), c'g, p'x, toA, (~*))
import Nil.Field (Field)
import Nil.Utils (Pretty (..), die)

data NIL i r q = NIL (Curve i q) (UL i r q)
  deriving (Eq, Show, Generic, NFData)

data UL i r q
  = U r -- Unlifted value
  | L (Point i q) -- Lifted value
  deriving (Eq, Show, Generic, NFData)

instance
  (Integral r, Field r, Integral q, Field q)
  => Num (NIL i r q)
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
  (Integral r, Field r, Integral q, Field q)
  => Fractional (NIL i r q)
  where
  recip = recip'
  {-# INLINE recip #-}

  (/) !a !b = a * recip b
  {-# INLINE (/) #-}

  fromRational = undefined

instance
  (Eq r, Ord r, Integral r, Integral q, Field q)
  => Ord (NIL i r q)
  where
  a <= b = unil a <= unil b

-- | nil
nil :: Curve i q -> r -> NIL i r q
nil c = NIL c . U
{-# INLINE nil #-}

-- | unil
unil :: (Integral r, Integral q, Field q) => NIL i r q -> r
unil nil = case unlift nil of
  NIL _ (U a) -> a
  a -> die "Error, failed to unload from NIL-object"
{-# INLINE unil #-}

-- | lift
lift :: (Integral r, Field q) => NIL i r q -> NIL i r q
lift (NIL c val) = case val of
  U a -> NIL c . L $ c'g c ~* a
  a -> NIL c a
{-# INLINE lift #-}

-- | unlift
unlift :: (Integral r, Integral q, Field q) => NIL i r q -> NIL i r q
unlift (NIL c val) = case val of
  L O -> NIL c . U $ 0
  L a -> NIL c . U . fromIntegral . fromJust . p'x $ a
  a -> NIL c a
{-# INLINE unlift #-}

-- | add
add :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
add a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL c . U $ x + y
  (L x, L y) -> NIL c . L $ x + y
  _ -> add (lift a) (lift b)
{-# INLINE add #-}

-- | sub
sub :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
sub a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL c . U $ x - y
  (L x, L y) -> NIL c . L $ x - y
  _ -> sub (lift a) (lift b)
{-# INLINE sub #-}

-- | mul
mul :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
mul a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL c . U $ x * y
  (U x, L y) -> NIL c . L $ y ~* x
  (L x, U y) -> NIL c . L $ x ~* y
  _ -> die "Error, undefined (*) operation between lifted values"
{-# INLINE mul #-}

-- | negate
negate' :: (Num r, Field q) => NIL i r q -> NIL i r q
negate' (NIL c val) = case val of
  U a -> NIL c . U . negate $ a
  L a -> NIL c . L . negate $ a
{-# INLINE negate' #-}

-- | reciprocal
recip' :: (Fractional r, Field q) => NIL i r q -> NIL i r q
recip' (NIL c val) = case val of
  U a -> NIL c . U . recip $ a
  a -> die "Error, undefined 'recip' operation on a lifted value"
{-# INLINE recip' #-}

instance (Show r, Show q, Pretty q, Field q) => Pretty (UL i r q) where
  pretty = \case
    U a -> show a
    L a -> pretty (toA a)

instance (Show r, Show q, Pretty q, Field q) => Pretty (NIL i r q) where
  pretty (NIL c val) = pretty val
