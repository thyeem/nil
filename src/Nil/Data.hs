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
  , p'from'ul
  , ul'from'p
  )
where

import Control.DeepSeq (NFData)
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Nil.Curve (Curve, Point (..), ap, c'g, p'x, toA, y'from'x, (~*))
import Nil.Field (Field)
import Nil.Utils (Pretty (..), die)

data NIL i r q = NIL (Curve i q) (UL r q)
  deriving (Eq, Show, Generic, NFData)

data UL r q
  = U r -- Unlifted value
  | L q Int -- Lifted value
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
lift :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q
lift (NIL c val) = case val of
  U a -> NIL c . ul'from'p $ c'g c ~* a
  a -> NIL c a
{-# INLINE lift #-}

-- | unlift
unlift :: (Integral r, Integral q, Field q) => NIL i r q -> NIL i r q
unlift (NIL c val) = case val of
  L _ 0 -> NIL c . U $ 0
  L a _ -> NIL c . U . fromIntegral $ a
  a -> NIL c a
{-# INLINE unlift #-}

-- | Encode EC point to NILdata
ul'from'p :: (Integral q, Field q) => Point i q -> UL r q
ul'from'p = \case
  O -> L 0 0
  A c x y -> L x (if even y then 2 else 3)
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
  (U x, U y) -> NIL c . U $ x + y
  (x@L {}, y@L {}) -> NIL c . ul'from'p $ p'from'ul c x + p'from'ul c y
  _ -> add (lift a) (lift b)
{-# INLINE add #-}

-- | sub
sub :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q -> NIL i r q
sub a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL c . U $ x - y
  (x@L {}, y@L {}) -> NIL c . ul'from'p $ p'from'ul c x - p'from'ul c y
  _ -> sub (lift a) (lift b)
{-# INLINE sub #-}

-- | mul
mul :: (Integral r, Field q, Integral q) => NIL i r q -> NIL i r q -> NIL i r q
mul a@(NIL c a_) b@(NIL _ b_) = case (a_, b_) of
  (U x, U y) -> NIL c . U $ x * y
  (U x, y@L {}) -> NIL c . ul'from'p $ p'from'ul c y ~* x
  (x@L {}, U y) -> NIL c . ul'from'p $ p'from'ul c x ~* y
  _ -> die "Error, undefined (*) operation between lifted values"
{-# INLINE mul #-}

-- | negate
negate' :: (Num r, Field q, Integral q) => NIL i r q -> NIL i r q
negate' (NIL c val) = case val of
  U a -> NIL c . U . negate $ a
  a@L {} -> NIL c . ul'from'p $ p'from'ul c a
{-# INLINE negate' #-}

-- | reciprocal
recip' :: (Fractional r, Field q) => NIL i r q -> NIL i r q
recip' (NIL c val) = case val of
  U a -> NIL c . U . recip $ a
  a -> die "Error, undefined 'recip' operation on a lifted value"
{-# INLINE recip' #-}

instance (Show r, Show q, Pretty q, Field q) => Pretty (UL r q) where
  pretty = \case
    U a -> show a
    L a parity -> show (a, parity)

instance (Show r, Show q, Pretty q, Field q) => Pretty (NIL i r q) where
  pretty (NIL c val) = pretty val
