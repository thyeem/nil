{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Nil.Data
  ( nil
  , unil
  , NIL
  , lift
  , unlift
  )
where

import Control.DeepSeq (NFData)
import Data.Maybe (fromJust)
import GHC.Generics (Generic)
import Nil.Curve (Curve, Point (O), c'g, p'x, toA, (.*))
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

  negate = neg
  {-# INLINE negate #-}

  fromInteger = undefined
  signum = undefined
  abs = undefined

-- | nil
nil :: Curve i q -> r -> NIL i r q
nil curve = NIL curve . U
{-# INLINE nil #-}

-- | unil
unil :: (Integral r, Integral q, Field q) => NIL i r q -> r
unil nil = case unlift nil of
  NIL _ (U a) -> a
  _ -> die "Error, failed to unload from NIL-object"
{-# INLINE unil #-}

-- | lift
lift :: (Integral r, Field q) => NIL i r q -> NIL i r q
lift (NIL curve val) = case val of
  U a -> NIL curve (L $ c'g curve .* a)
  a -> NIL curve a
{-# INLINE lift #-}

-- | unlift
unlift :: (Integral r, Integral q, Field q) => NIL i r q -> NIL i r q
unlift (NIL curve val) = case val of
  L O -> NIL curve (U 0)
  L a -> NIL curve (U . fromIntegral . fromJust . p'x $ a)
  a -> NIL curve a
{-# INLINE unlift #-}

-- | add
add :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
add a@(NIL curve a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL curve (U $ x + y)
  (L x, L y) -> NIL curve (L $ x + y)
  (x, y) -> add (lift a) (lift b)
{-# INLINE add #-}

-- | sub
sub :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
sub a@(NIL curve a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL curve (U $ x - y)
  (L x, L y) -> NIL curve (L $ x - y)
  (x, y) -> sub (lift a) (lift b)
{-# INLINE sub #-}

-- | mul
mul :: (Integral r, Field q) => NIL i r q -> NIL i r q -> NIL i r q
mul a@(NIL curve a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL curve (U $ x * y)
  (U x, L y) -> NIL curve (L $ y .* x)
  (L x, U y) -> NIL curve (L $ x .* y)
  (L _, L _) -> die "Error, undefined (*) operation between lifted values"
{-# INLINE mul #-}

-- | neg
neg :: (Num r, Field q) => NIL i r q -> NIL i r q
neg (NIL curve val) = case val of
  U a -> NIL curve (U . negate $ a)
  L a -> NIL curve (L . negate $ a)
{-# INLINE neg #-}

instance (Show r, Show q, Pretty q, Field q) => Pretty (UL i r q) where
  pretty = \case
    U a -> show a
    L a -> pretty (toA a)

instance (Show r, Show q, Pretty q, Field q) => Pretty (NIL i r q) where
  pretty (NIL curve val) = pretty val
