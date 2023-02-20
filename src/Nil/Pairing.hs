{-# OPTIONS -Wno-unused-top-binds #-}
{-# LANGUAGE LambdaCase #-}

module Nil.Pairing
  ( miller'loop
  , twist
  , pairing
  , from'fq
  )
where

import Data.List (foldl')
import Nil.Curve
  ( Curve (..)
  , Point (..)
  , frobp
  , jp
  , toJ
  , (.*)
  )
import Nil.Ecdata
  ( BN254
  , G1
  , G2
  , GT
  , bn254'g1
  , bn254'gt
  , field'gt
  )
import Nil.Field
  ( Extensionfield (..)
  , Field (..)
  )
import Nil.Utils
  ( bits'from'int
  , die
  , (|+|)
  )

{-
 BN curve can be parametrized as following:
 char of prime field q, group order r, trace of Frobenius tr
 q(t) = 36*t^4 + 36*t^3 + 24*t^2 + 6*t + 1
 r(t) = 36*t^4 + 36*t^3 + 18*t^2 + 6*t + 1
 tr(t) = 6t^2 + 1

 An arbitrary integer t such that p(t) and r(t) are both prime number
 Large enough t required for an adequate security level
 AES-128-equiv security level: log2(r(t)) > 256 ~ 64bit t
 t = 4965661367192848881

 E[r]: r-torsion subgroup of E
 pi: Frobenius endomorphism, pi_q(x, y) = (x^q, y^q), pi_q: E -> E
 G1: E[r] & Ker(pi_q - [1])
 G2: E[r] & Ker(pi_q - [q])
 G1, G2 in E(Fq^12)[r]
 GT: mu_r in *Fq^12 (the group of r-th root of unity)

 aOpt: G2 x G1 -> GT
       (Q, P) |-> ( f_[6t+2,Q](P) .
                    l_[(6t+2)Q, pi_q(Q)](P) .
                    l_[(6t+2)Q + pi_q(Q), -pi_q^2(Q)](P) ) ^ (q^12 - 1)/r
-}

-- | 6t + 2
loop'count :: Integer
loop'count = 29793968203157093288

-- | Element-wise operation of (*) on 2-elem tuples
(*|*) :: Num a => (a, a) -> (a, a) -> (a, a)
ta *|* tb = (o * q, p * r) where ((o, p), (q, r)) = (ta, tb)

{- | Miller's algorithm based on optimal Ate pairing:  aT(Q, P) -> f
 https://eprint.iacr.org/2010/354.pdf
 https://eprint.iacr.org/2016/130.pdf
-}
miller'loop :: Point BN254 GT -> Point BN254 GT -> GT
miller'loop p q
  | p == O || q == O = field'gt [1]
  | otherwise = final'exp . uncurry (/) . finalQ2 . finalQ1 $ loop
 where
  loop = foldl' (add . dbl) ((field'gt [1], field'gt [1]), q) s
  s = drop 1 . reverse $ bits'from'int loop'count
  frobQ1 = frobp q (1 :: Int)
  frobQ2 = negate . frobp q $ (2 :: Int)
  finalQ1 (f, t) = (f *|* linefunc t frobQ1 p, t |+| frobQ1)
  finalQ2 (f, t) = f *|* linefunc t frobQ2 p
  dbl (f, t) = (f *|* f *|* linefunc t t p, t .* (2 :: Int))
  add (f, t) b
    | b == 1 = (f *|* linefunc t q p, t |+| q)
    | otherwise = (f, t)
{-# INLINEABLE miller'loop #-}

-- dbl'step :: ((GT, GT), Point GT) -> ((GT, GT), Point GT)
-- dbl'step (f, t) = (f *|* f *|* linefunc t t p, t .* 2)

{- | A function f representing the line through P and Q
 Returns values from the function evaluation at point T: f(T)
 Separately update the numerator and the denominator of f(T),
 to avoid frequent reciprocal operations.
-}
linefunc
  :: (Eq f, Fractional f, Field f)
  => Point i f
  -> Point i f
  -> Point i f
  -> (f, f)
linefunc p q t = linefuncJ (toJ p) (toJ q) (toJ t)

-- | LineFunction based on Affine coordinates
linefuncA
  :: (Eq f, Fractional f, Field f)
  => Point i f
  -> Point i f
  -> Point i f
  -> (f, f)
linefuncA = go
 where
  go x y z | x == O || y == O || z == O = die "Not defined at O"
  go (A _ x1 y1) (A _ x2 y2) (A _ xt yt)
    | x1 /= x2 = (lu * (xt - x1) - lb * (yt - y1), lb)
    | y1 == y2 = (lu' * (xt - x1) - lb' * (yt - y1), lb')
    | otherwise = (xt - x1, 1)
   where
    lu = y2 - y1
    lb = x2 - x1
    lu' = e3 * x1 * x1
    lb' = e2 * y1
    e = one x1
    e2 = e + e
    e3 = e2 + e
  go _ _ _ = die "Invalid points used: "
{-# INLINEABLE linefuncA #-}

-- | LineFunction based on Jacobian coordinates
linefuncJ
  :: (Eq f, Fractional f, Field f)
  => Point i f
  -> Point i f
  -> Point i f
  -> (f, f)
linefuncJ = go
 where
  go x y z | x == O || y == O || z == O = die "Not defined at O"
  go (J _ x1 y1 z1) (J _ x2 y2 z2) (J _ xt yt zt)
    | (x1 * z2 ^ (2 :: Int)) /= (x2 * z1 ^ (2 :: Int)) =
        (lu * a * b - lb * d, lb * g)
    | otherwise =
        (lu' * a * b - lb' * d, lb' * g)
   where
    lu = z1 ^ (3 :: Int) * y2 - z2 ^ (3 :: Int) * y1
    lb = z1 * z2 * (z1 ^ (2 :: Int) * x2 - z2 ^ (2 :: Int) * x1)
    lu' = e3 * x1 * x1
    lb' = e2 * y1 * z1
    a = z1 * zt
    b = z1 ^ (2 :: Int) * xt - zt ^ (2 :: Int) * x1
    d = z1 ^ (3 :: Int) * yt - zt ^ (3 :: Int) * y1
    g = (z1 * zt) ^ (3 :: Int)
    e = one x1
    e2 = e + e
    e3 = e2 + e
  go _ _ _ = die "Invalid points used: "
{-# INLINEABLE linefuncJ #-}

-- | Final exponentiation
final'exp :: GT -> GT
final'exp f = f ^ expo
 where
  expo = (c'p bn254'g1 ^ (12 :: Int) - 1) `div` c'n bn254'g1
{-# INLINE final'exp #-}

{- | Reduced Tate pairing using optimal Ate pairing
 P in G1 x Q in G2 -> e(P, Q)
-}
pairing :: Point BN254 G1 -> Point BN254 G2 -> GT
-- pairing p q = go (toJ p) (toJ q)
pairing p q = miller'loop (from'fq p) (twist q)
{-# INLINE pairing #-}

-- | Construct a point on GT from a point on G1
from'fq :: Point BN254 G1 -> Point BN254 GT
from'fq = \case
  J _ x y z -> jp bn254'gt (field'gt [x]) (field'gt [y]) (field'gt [z])
  O -> O
  a -> from'fq (toJ a)
{-# INLINE from'fq #-}

-- | Map G2, E(Fq^2) point to its sextic twist GT, E(Fq^12) point
twist :: Point BN254 G2 -> Point BN254 GT
twist = \case
  O -> O
  a@A {} -> twist (toJ a)
  J _ (E _ x) (E _ y) (E _ z) ->
    let [x0, x1] = x + [0, 0]
        [y0, y1] = y + [0, 0]
        [z0, z1] = z + [0, 0]
        xt = field'gt [x0 - 9 * x1, 0, 0, 0, 0, 0, x1] * field'gt [0, 0, 1]
        yt = field'gt [y0 - 9 * y1, 0, 0, 0, 0, 0, y1] * field'gt [0, 0, 0, 1]
        zt = field'gt [z0 - 9 * z1, 0, 0, 0, 0, 0, z1]
     in jp bn254'gt xt yt zt
{-# INLINE twist #-}
