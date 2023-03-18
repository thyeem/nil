{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Nil.Poly
  ( addpoly,
    subpoly,
    scalepoly,
    (|*),
    mulpoly,
    divpoly,
    (|/),
    powpoly,
    evalpoly,
    (|=),
    egcdpoly,
    randpoly,
    (|?),
    (-*-),
    (||*),
    (<.>),
    (<|.>),
    lagrangepoly,
    lagrangebases,
    evalLagrangepoly,
    evalLagrangepoly',
  )
where

import Control.DeepSeq (NFData)
import Control.Exception
  ( ArithException (..),
    throw,
  )
import Control.Monad (replicateM)
import Data.Bifunctor (Bifunctor (first))
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List
  ( dropWhileEnd,
    foldl',
  )
import Nil.Utils
  ( Pretty (..),
    die,
    pfold,
    pzip'with,
  )
import System.Random
  ( Random (..),
    newStdGen,
    randomRIO,
  )

-- | Monic polynomial representation
-- The least significant coefficient is at leftmost in the coeffs-list
-- f(x) := c0 + c1*x + ... + ck*x^k = [c0,c1,..,ck]
instance (Eq p, Num p) => Num [p] where
  (+) = addpoly
  {-# INLINE (+) #-}

  (-) = subpoly
  {-# INLINE (-) #-}

  (*) = mulpoly
  {-# INLINE (*) #-}

  negate = flip scalepoly (-1)
  {-# INLINE negate #-}

  fromInteger = (: []) . fromIntegral
  signum = undefined
  abs = undefined

instance (Eq p, Fractional p) => Fractional [p] where
  f / g = fst $ divpoly f g
  {-# INLINE (/) #-}

  recip = undefined
  fromRational = undefined

deriving instance (Show p) => Pretty [p]

-- | Pairwise binary opteration with the same-degree zipped coefficients.
-- This is different from 'zipWith' as this function plays with the longest one.
zip'with :: (Eq p, Num p) => (p -> p -> p) -> [p] -> [p] -> [p]
zip'with op = go
  where
    go r@(_ : _) [] = r
    go [] r@(_ : _) = op 0 <$> r
    go [] [] = []
    go (x : xs) (y : ys) = op x y : go xs ys
{-# INLINE zip'with #-}

-- | f(x) + g(x)
addpoly :: (Eq p, Num p) => [p] -> [p] -> [p]
addpoly = zip'with (+)
{-# INLINE addpoly #-}

-- | f(x) - g(x)
subpoly :: (Eq p, Num p) => [p] -> [p] -> [p]
subpoly = zip'with (-)
{-# INLINE subpoly #-}

-- | f(x) * g(x)
mulpoly :: (Eq p, Num p) => [p] -> [p] -> [p]
mulpoly [] _ = []
mulpoly (x : xs) ys = (ys |* x) + (0 : xs * ys)
{-# INLINE mulpoly #-}

-- | f(x) * k
scalepoly :: (Eq p, Num p) => [p] -> p -> [p]
scalepoly f x = trim $ (* x) <$> f
{-# INLINE scalepoly #-}

-- | Infix scalepoly
(|*) :: (Eq p, Num p) => [p] -> p -> [p]
(|*) = scalepoly
{-# INLINE (|*) #-}

-- | Eliminate leading-zero coefficients from LE-form polynomial
trim :: (Eq a, Num a) => [a] -> [a]
trim = dropWhileEnd (== 0)
{-# INLINE trim #-}

-- | f(x) / g(x)
-- Divide polynomials one another, then returns (quotient, remainder)
divpoly :: (Eq p, Fractional p) => [p] -> [p] -> ([p], [p])
divpoly f g = uncurry (on (,) (trim . reverse)) (go (reverse f) (reverse g))
  where
    go _ [] = throw DivideByZero
    go [] _ = ([], [])
    go n@(x : _) d@(y : _)
      | length n < length d = ([], n)
      | otherwise = first (q :) (go (drop 1 r) d)
      where
        q = x / y
        r = n - (d |* q)
{-# INLINE divpoly #-}

-- | Infix divpoly
(|/) :: (Eq p, Fractional p) => [p] -> [p] -> ([p], [p])
(|/) = divpoly
{-# INLINE (|/) #-}

-- | f(x) ^ k: Integer exponentiation
powpoly :: (Eq p, Num p, Integral a) => [p] -> a -> [p]
powpoly f k
  | k < 0 = die "Negative exponent"
  | k == 0 = [1]
  | k == 1 = f
  | even k = g * g
  | otherwise = f * (g * g)
  where
    g = powpoly f (div k 2)
{-# INLINE powpoly #-}

-- | Evaluate the polynomial at a given x: f(x)
evalpoly :: (Eq p, Num p, NFData p) => [p] -> p -> p
evalpoly poly x = foldl' (\acc c -> acc * x + c) 0 (reverse poly)
{-# INLINE evalpoly #-}

-- | Infix evalpoly
(|=) :: (Eq p, Num p, Integral p, NFData p) => [p] -> p -> p
(|=) = evalpoly
{-# INLINE (|=) #-}

-- | Hadamard product or element-wise product of the same-sized two vectors:
--
-- [a,b,c] -*- [i,j,k] = [ai,bj,ck]
(-*-) :: (Eq p, Num p, Monoid p, NFData p) => [p] -> [p] -> [p]
(-*-) = pzip'with (*)
{-# INLINE (-*-) #-}

-- | Hadamard product-like element-size product with a vector and a scalar element:
--
-- [ [a1,a2], [b1,b2] ] ||* [i,j]
-- = [ [a1,a2]*i, [b1,b2]*j ]
(||*) :: (Eq p, Num p, NFData p) => [[p]] -> [p] -> [[p]]
(||*) = pzip'with (|*)
{-# INLINE (||*) #-}

-- | Inner product of two polynomials or vectors
--
-- [a,b,c] <.> [i,j,k] = sum [ai,bj,ck] = ai + bj + ck
(<.>) :: (Eq p, Num p, Monoid p, NFData p) => [p] -> [p] -> p
(<.>) = (pfold (+) .) . (-*-)
{-# INLINE (<.>) #-}

-- | Inner product of a polynomial vector and a polynomial
-- [ [a1,a2], [b1,b2] ] <|.> [i,j]
-- = sum [ [a1,a2]*i, [b1,b2]*j ]
-- = [a1,a2]*i + [b1,b2]*j
(<|.>) :: (Eq p, Num p, NFData p) => [[p]] -> [p] -> [p]
(<|.>) = (pfold (+) .) . (||*)
{-# INLINE (<|.>) #-}

-- | Extended Euclidean algorithm for polynomial
--  Find (a,b) holding f(x)*a(x) + g(x)*b(x) = gcd(f(x),g(x)).
--
--  If p is None, the process is performed in the ring of polynomials
--  with rational coefficients (Q). Otherwise, it works with the polynomials
--  with integer coefficients modulo p, (Z/pZ).
--
--  If p is a prime number, it works with the polynomials over GF(p)
egcdpoly :: (Eq p, Fractional p) => [p] -> [p] -> ([p], [p])
egcdpoly _ [] = ([1], [])
egcdpoly a b = (y, x - (q * y))
  where
    (q, r) = a |/ b
    (x, y) = egcdpoly b r
{-# INLINE egcdpoly #-}

-- | Construct Lagrange interpolating polynomial with given points
lagrangepoly :: (Eq p, Fractional p) => [(p, p)] -> [p]
lagrangepoly xys = pfold (+) $ zipWith (|*) (lagrangebases xs) ys
  where
    (xs, ys) = unzip xys
{-# INLINE lagrangepoly #-}

-- | Construct Lagrange bases from the x-coord set of points
lagrangebases :: (Eq p, Fractional p) => [p] -> [[p]]
lagrangebases xs = basisPoly <$> xs
  where
    basisPoly x = pfold (*) $ weightedRoot x <$> xs
    weightedRoot xj xm
      | xj == xm = [1]
      | otherwise = (|*) [-xm, 1] $ 1 / (xj - xm)

-- | Evalutate Lagrange polynomial at a given x-coord
-- Polynomial interpolation for numerical analysis
evalLagrangepoly ::
  (Eq p, Integral p, Fractional p, NFData p) => [(p, p)] -> p -> p
evalLagrangepoly = evalpoly . lagrangepoly

-- | Same as 'evalLagrangepoly',
-- but much faster way to interpolate as it just focuses on weight calculation
evalLagrangepoly' :: (Eq p, Fractional p, NFData p) => [(p, p)] -> p -> p
evalLagrangepoly' xys x = sum $ zipWith (*) ys $ basisEval <$> xs
  where
    (xs, ys) = unzip xys
    basisEval xj = product (weightEval xj <$> xs)
    weightEval xj xm
      | xj == xm = 1
      | otherwise = (x - xm) / (xj - xm)

-- | Generate a Random Polynomial of k-1 degree at most.
randpoly :: (Random p) => Int -> IO [p]
randpoly n = (newStdGen <&> randoms) <&> take n

-- | Generate a Random Polynomial of k-1 degree at most with range
(|?) :: (Num p, Random p, Integral a) => (a, a) -> Int -> IO [p]
(|?) (low, high) n =
  (fromInteger <$>)
    <$> sequence (replicateM n randomRIO (toInteger low, toInteger high))
