{-# LANGUAGE LambdaCase #-}

module Nil.C where

import Control.DeepSeq (NFData)
import Nil.Curve
import Nil.Field
import Nil.Utils (die)

data Nildata r q
  = U r -- Unlifted data
  | L (Point q) -- Lifted data
  deriving (Eq, Show)

-- instance (Num r, Eq q, Fractional q, Field q, NFData q) => Num (Nildata r q) where

lift :: (Integral r, Field q) => Curve q -> Nildata r q -> Point q
lift curve = \case
  U a -> mulg curve a
  L a -> die "Error, cannot lift the lifted already"
