{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Nil.C where

import Control.DeepSeq (NFData)
import Nil.Curve
import Nil.Ecdata (BN254, G1)
import Nil.Field
import Nil.Utils (die)

data Nildata i r q
  = U r -- Unlifted data
  | L (Point i q) -- Lifted data
  deriving (Eq, Show)

-- instance (Num r, Field q) => Num (Nildata r q) where

lift :: (Integral r, Field q) => Nildata i r q -> Point i q
lift = \case
  L a -> die "Error, cannot lift the lifted already"
  U a -> f
   where
    f = mulg (curve'from'p f) a

curve'from'p :: Point i f -> Curve i f
curve'from'p = \case
  O -> die "Error,"
  A c _ _ -> c
  J c _ _ _ -> c

type Francis = Nildata BN254 (Primefield 83) G1
