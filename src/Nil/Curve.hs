{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS -Wno-unused-top-binds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

-- | Defines @Weierstrass Elliptic@ 'Curve' and 'Point' over @/GF(p)/@
module Nil.Curve where

-- ( Point (..)
-- , Curve (..)
-- , c'g
-- , ap
-- , ap'
-- , jp
-- , jp'
-- , toA
-- , toJ
-- , p'x
-- , p'y
-- , oncurve
-- , atinf
-- , yfromx
-- , findp
-- , (.*)
-- , (<.*>)
-- , addp
-- , dblp
-- , invp
-- , mulp
-- , subp
-- , mulg
-- , apbq'sum
-- , randp
-- , frobp
-- )

import Control.DeepSeq (NFData)
import Data.List (nub)
import GHC.Generics (Generic)
import Nil.Base (sqrt'zpz)
import Nil.Field (Field (..), Primefield)
import Nil.Utils
  ( Pretty (..)
  , die
  , pfold
  , pzip'with
  , (<%>)
  , (|+|)
  )
import System.Random (randomRIO)

{- | Elliptic Curve over @/GF(p)/@ in short Weierstrass form: @y^2 = x^3 + a*x + b@
 @
 +--------+-------------------------------------------------------------------+
 | @c'p@  | Characteristic of curve                                           |
 +--------+-------------------------------------------------------------------+
 | @c'a@  | Coefficient @a@ in the curve equation                             |
 +--------+-------------------------------------------------------------------+
 | @c'b@  | Coefficient @b@ in the curve equation                             |
 +--------+-------------------------------------------------------------------+
 | @c'gx@ | Affine @x@-coordinate of @G@, the base point of an elliptic curve |
 +--------+-------------------------------------------------------------------+
 | @c'gy@ | Affine @y@-coordinate of @G@, the base point of an elliptic curve |
 +--------+-------------------------------------------------------------------+
 | @c'n@  | Size of group of @/E(Fp)/@, @|/E(Fp)/|@                           |
 +--------+-------------------------------------------------------------------+
 | @c'h@  | Curve cofactor = @|/E(Fp)/| / n@, size of subgroup of @/E(Fp)/@   |
 +--------+-------------------------------------------------------------------+
 @
-}
data Curve i f = Curve
  { c'name :: String
  , c'p :: Integer
  , c'a :: f
  , c'b :: f
  , c'gx :: f
  , c'gy :: f
  , c'n :: Integer
  , c'h :: Integer
  }
  deriving (Eq, Show, Read, Generic, NFData)

{- | Points on Elliptic Curve
 @
 +-----+---------------------------------------------------------------------------+
 | @A@ | Constructor representing Affine point, @(x, y)@                           |
 +-----+---------------------------------------------------------------------------+
 | @J@ | Constructor representing Jacobian point, @(x, y) = (X/Z^2, Y/Z^3, Z)@     |
 +-----+---------------------------------------------------------------------------+
 | @O@ | Point at Infinity                                                         |
 +-----+---------------------------------------------------------------------------+
 @
 @O@ in Jacobian coordinates: @(X,Y,Z) = (t^2,t^3,0) = (1,1,0)@ when @t = 1@
-}
data Point i f
  = A (Curve i f) f f
  | J (Curve i f) f f f
  | O
  deriving (Show, Read, Generic, NFData)

-- | Definition of Point Equality
instance Field f => Eq (Point c f) where
  (==) = f
   where
    f (A _ x1 y1) (A _ x2 y2) = x1 == x2 && y1 == y2
    f p O = atinf p
    f O p = atinf p
    f p1 p2 = f (toA p1) (toA p2)
  {-# INLINE (==) #-}

-- Equality test for Jacobian point
-- f (J _ x1 y1 z1) (J _ x2 y2 z2) =
--   x1 * z2 ^ 2 == x2 * z1 ^ 2 && y1 * z2 ^ 3 == y2 * z1 ^ 3

instance Field f => Semigroup (Point c f) where
  (<>) = (+)

instance Field f => Monoid (Point c f) where
  mempty = O

instance Field f => Num (Point c f) where
  (+) !p !q = addp p q
  {-# INLINE (+) #-}

  (-) !p !q = subp p q
  {-# INLINE (-) #-}

  negate = invp
  {-# INLINE negate #-}

  (*) = die "Error, undefined (*) between two elliptic points"
  fromInteger = undefined
  signum = undefined
  abs = undefined

-- | Construct an @Affine@ point
ap :: Field f => Curve i f -> f -> f -> Point i f
ap curve x y = A curve (e * x) (e * y) where e = one x

-- | Construct an @Affine@ point with a on-curve checkup
ap' :: Field f => Curve i f -> f -> f -> Point i f
ap' curve x = checkup . ap curve x
 where
  checkup p
    | oncurve p = p
    | otherwise = die "Error, not on curve"

-- | Constructor a @Jacobian@ point
jp :: Field f => Curve i f -> f -> f -> f -> Point i f
jp curve x y z
  | atinf p = O
  | otherwise = p
 where
  p = J curve (e * x) (e * y) (e * z)
  e = one x

-- | Constructor a @Jacobian@ point with a on-curve checkup
jp' :: Field f => Curve i f -> f -> f -> f -> Point i f
jp' curve x y = checkup . jp curve x y
 where
  checkup p
    | oncurve p = p
    | otherwise = die "Error, not on curve"

-- | Convert @Jacobian@ point into @Affine@ point
toA :: Field f => Point i f -> Point i f
toA p = case p of
  A {} -> p
  O -> O
  J curve x y z
    | atinf p -> O
    | otherwise -> A curve (x / z ^ (2 :: Int)) (y / z ^ (3 :: Int))
{-# INLINE toA #-}

-- | Convert @Affine@ point into @Jacobian@ point
toJ :: Field f => Point i f -> Point i f
toJ p = case p of
  A curve x y -> jp curve x y (one x)
  _ -> p
{-# INLINE toJ #-}

-- | Get the defined base point or the generator from a given elliptic curve
c'g :: Field f => Curve i f -> Point i f
c'g curve = A curve (c'gx curve) (c'gy curve)
{-# INLINE c'g #-}

{- | Check if a given point is on the elliptic curve defined

 True if @y^2 = x^3 + a*x + b@ holds over the finite field
-}
oncurve :: Field f => Point i f -> Bool
oncurve p = case p of
  O -> True
  (A curve x y) -> y * y == (x * x + c'a curve) * x + c'b curve
  (J curve x y z) ->
    (y * y)
      == ((x * x + c'a curve * z ^ (4 :: Int)) * x + c'b curve * z ^ (6 :: Int))
{-# INLINEABLE oncurve #-}

-- | Check if a given point is @__Point at Infinity__@ or not
atinf :: Field f => Point i f -> Bool
atinf p = case p of
  O -> True
  J _ x y z
    | z == zero z && (x ^ (3 :: Int)) == (y ^ (2 :: Int)) -> True
    | otherwise -> False
  _ -> False
{-# INLINEABLE atinf #-}

-- | Get @Affine@ @x@-coordinate from an elliptic curve point
p'x :: Field f => Point i f -> Maybe f
p'x = \case
  O -> Nothing
  A _ x _ -> Just x
  p -> p'x . toA $ p
{-# INLINE p'x #-}

-- | Get @Affine@ @x@-coordinate from an elliptic curve point
p'y :: Field f => Point i f -> Maybe f
p'y = \case
  O -> Nothing
  A _ _ y -> Just y
  p -> p'y . toA $ p
{-# INLINE p'y #-}

-- | Point scalar multiplication infix operator
(.*) :: (Field f, Integral a) => Point i f -> a -> Point i f
(.*) = mulp
{-# INLINE (.*) #-}

{- | Inner product or weighted sum with the given point and weight vectors
 For arbitrary points P, Q, and R on curve E(Fq),
 [P,Q,R] <:> [3,5,7] = (P *: 3) + (Q *: 5) + (R *: 7)
-}
(<.*>) :: (Field f, Integral a, NFData a) => [Point i f] -> [a] -> Point i f
(<.*>) = (pfold (+) .) . pzip'with (.*)
{-# INLINE (<.*>) #-}

-- | Point addition
addp :: Field f => Point i f -> Point i f -> Point i f
addp a b = addjp (toJ a) (toJ b)
{-# INLINE addp #-}

-- | Point doubling
dblp :: Field f => Point i f -> Point i f
dblp p = dbljp (toJ p)
{-# INLINE dblp #-}

-- | Flip point on x-axis
invp :: Field f => Point i f -> Point i f
invp (J curve x y z) = jp curve x (-y) z
invp (A curve x y) = ap curve x (-y)
invp O = O
{-# INLINE invp #-}

-- | Point scalar multiplication using 'double and add algorithm'
mulp :: (Field f, Integral a) => Point i f -> a -> Point i f
mulp p = go (toJ p)
 where
  go O _ = O
  go _ 0 = O
  go p' 1 = p'
  go p' n
    | n < 0 = die "Error, negative exponent"
    | even n = dbljp g
    | otherwise = p' |+| dbljp g
   where
    g = p' `mulp` (n `div` 2)
{-# INLINE mulp #-}

-- | Point substraction
subp :: Field f => Point i f -> Point i f -> Point i f
subp p q = p |+| invp q
{-# INLINE subp #-}

-- | Point scalar mutiplication with curve generator point
mulg :: (Field f, Integral a) => Curve i f -> a -> Point i f
mulg curve n = g .* n where g = c'g curve
{-# INLINE mulg #-}

{- | Point multiplication using Strauss-Shamir method or Shamir's trick
 For those given (a,P) and (b,Q), efficiently evaluate (a *: P) +: (b *: Q)
-}
apbq'sum :: (Field f, Integral a) => (Point i f, a) -> (Point i f, a) -> Point i f
apbq'sum (p, a) (q, b) = go (toJ p, a) (toJ q, b)
 where
  go (O, _) (O, _) = O
  go (p', a') (O, _) = p' .* a'
  go (O, _) (q', b') = q' .* b'
  go (_, a') (_, b') = g a' b'
   where
    r = p + q
    g 0 0 = O
    g n m = case (odd n, odd m) of
      (True, True) -> z + r
      (True, False) -> z + p
      (False, True) -> z + q
      (False, False) -> z
     where
      z = dbljp $ g (n `div` 2) (m `div` 2)
{-# INLINEABLE apbq'sum #-}

{- | i-th power of Frobenius endomorphism for points on elliptic curve
 pi_q: E(Fq) -> E(Fq)
 pi(x, y) -> (x^(q^i), y^(q^i))
-}
frobp :: (Field f, Integral a) => Point i f -> a -> Point i f
frobp p i = case toJ p of
  O -> O
  J curve x y z ->
    let frobx = frob x (toInteger i)
        froby = frob y (toInteger i)
        frobz = frob z (toInteger i)
     in jp curve frobx froby frobz
  _ -> die "Error, no such endomorphism"
{-# INLINEABLE frobp #-}

-- | Pick a random point from a given curve
randp :: Field f => Curve i f -> IO (Point i f)
randp curve = do
  k <- randomRIO (1, c'n curve - 1)
  return $ mulg curve k

-- | Point addition (Affine Point)
addap :: Field f => Point i f -> Point i f -> Point i f
addap p O = p
addap O q = q
addap p1@(A curve x1 y1) p2@(A _ x2 y2)
  | p1 == p2 = dblap p1
  | p1 == invp p2 = O
  | otherwise = ap curve x3 y3
 where
  l = (y1 - y2) / (x1 - x2)
  x3 = l * l - x1 - x2
  y3 = l * (x1 - x3) - y1
addap _ _ = die "Error, invalid points used"
{-# INLINEABLE addap #-}

-- | Point doubling (Affine Point)
dblap :: Field f => Point i f -> Point i f
dblap O = O
dblap (A curve x y)
  | y == zero y = O
  | otherwise = ap curve x' y'
 where
  l = (e3 * x * x + a) / (e2 * y)
  a = c'a curve
  e = one x
  e2 = e + e
  e3 = e2 + e
  x' = l * l - x - x
  y' = l * (x - x') - y
dblap _ = die "Error, invalid points used"
{-# INLINEABLE dblap #-}

{- | Point addition (Jacobian Point)
 The "add-2007-bl" Addition Explicit Formula: 2007 Bernstein–Lange
 Cost: 11M + 5S + 9add + 4*2
-}
addjp :: Field f => Point i f -> Point i f -> Point i f
addjp p O = p
addjp O q = q
addjp p1@(J curve x1 y1 z1) p2@(J _ x2 y2 z2)
  | p1 == p2 = dbljp p1
  | otherwise = jp curve x3 y3 z3
 where
  z1z1 = z1 ^ (2 :: Int)
  z2z2 = z2 ^ (2 :: Int)
  u1 = x1 * z2z2
  u2 = x2 * z1z1
  s1 = y1 * z2 * z2z2
  s2 = y2 * z1 * z1z1
  h = u2 - u1
  i = (h + h) ^ (2 :: Int)
  j = h * i
  r = e2 * (s2 - s1)
  v = u1 * i
  x3 = r ^ (2 :: Int) - j - (v + v)
  y3 = r * (v - x3) - e2 * s1 * j
  z3 = ((z1 + z2) ^ (2 :: Int) - z1z1 - z2z2) * h
  e = one x1
  e2 = e + e
addjp _ _ = die "Error, invalid points used"
{-# INLINEABLE addjp #-}

{- | Point doubling (Jacobian Point)
 The "dbl-2007-bl" Doubling Explicit Formula: 2007 Bernstein–Lange
 Cost: 1M + 8S + 1*a + 10add + 2*2 + 1*3 + 1*8
-}
dbljp :: Field f => Point i f -> Point i f
dbljp O = O
dbljp (J curve x1 y1 z1) = jp curve x3 y3 z3
 where
  xx = x1 ^ (2 :: Int)
  yy = y1 ^ (2 :: Int)
  yyyy = yy ^ (2 :: Int)
  zz = z1 ^ (2 :: Int)
  s = e2 * ((x1 + yy) ^ (2 :: Int) - xx - yyyy)
  m = e3 * xx + a * zz ^ (2 :: Int)
  t = m ^ (2 :: Int) - e2 * s
  x3 = t
  y3 = m * (s - t) - e8 * yyyy
  z3 = (y1 + z1) ^ (2 :: Int) - yy - zz
  a = c'a curve
  e = one x1
  e2 = e + e
  e3 = e2 + e
  e4 = e2 + e2
  e8 = e4 + e4
dbljp _ = die "Error, invalid points used"
{-# INLINEABLE dbljp #-}

{- | Get @y@ coordinate of a @Affine@ point on curve from @x@

 Used Tonelli-Shanks method to calculate @Sqrt@ over @/GF(p)/@
-}
yfromx :: (Integral f, Field f) => Curve i f -> f -> Maybe (f, f)
yfromx curve x = case a of
  Just s -> Just (fromInteger s, fromInteger . negate $ s)
  Nothing -> Nothing
 where
  a = sqrt'zpz (toInteger $ (x * x + c'a curve) * x + c'b curve) (char x)

-- | Find all points on a given curve using brute-force method
findp
  :: (Integral f, Bounded f, Field f)
  => Curve i f
  -> [Point i f]
findp curve =
  O
    : ( nub
          . concat
          $ [ split (x, y, y')
            | (x, Just (y, y')) <-
                (\x -> (x,) (yfromx curve x)) <%> [minBound .. maxBound]
            ]
      )
 where
  split (x, y, y')
    | y == zero y = [A curve x y]
    | otherwise = [A curve x y, A curve x y']

instance (Show f, Pretty f) => Pretty (Curve i f)

instance (Show f, Pretty f) => Pretty (Point c f) where
  pretty = \case
    O -> "Point at Infinity"
    A c x y -> unlines [c'name c, pretty x, pretty y]
    J c x y z -> unlines [c'name c, pretty x, pretty y, pretty z]
