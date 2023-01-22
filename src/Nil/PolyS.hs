{-# LANGUAGE RecordWildCards #-}

module Nil.PolyS where

-- ( poly
-- , poly'
-- , nilpoly
-- , atmostc
-- , nilc
-- , nil
-- , shiftp
-- , addpoly
-- , subpoly
-- , scalepoly
-- , (|*)
-- , mulpoly
-- , divpoly
-- , (|/)
-- , powpoly
-- , evalpoly
-- , (|=)
-- ) where

import Control.Exception
  ( ArithException (..)
  , throw
  )
import Data.Bifunctor (first)
import Data.List (foldl')
import qualified Data.Map as M
import Nil.Utils (die)

{- | Monic polynomial representation
 The least significant coefficient is at leftmost in the coeffs-list
 f(x) := c0 + c1*x + ... + ck*x^k = [c0,c1,..,ck]

 The same as 'Zkbang.Poly, but this is for sparse polymonials
 'coeff' hashmap traces only non-zero coefficients with 'degree' Int key
-}
data Poly p = Poly
  { coeff :: M.Map Int p
  , deg :: Int
  }
  deriving (Eq, Ord)

instance (Eq p, Num p) => Num (Poly p) where
  (+) = addpoly
  {-# INLINE (+) #-}

  (-) = subpoly
  {-# INLINE (-) #-}

  (*) = mulpoly
  {-# INLINE (*) #-}

  negate = flip scalepoly (-1)
  {-# INLINE negate #-}

  fromInteger = poly . (: []) . fromIntegral
  signum = undefined
  abs = undefined

instance (Eq p, Fractional p) => Fractional (Poly p) where
  f / g = fst $ divpoly f g
  {-# INLINE (/) #-}

  recip = undefined
  fromRational = undefined

instance (Num p, Show p) => Show (Poly p) where
  show p = show $ getc p <$> [0 .. deg p]

-- | Construct a polynomial with a given list of coeffs
poly :: (Eq p, Num p) => [p] -> Poly p
poly xs = poly' (zip [0 ..] xs)
{-# INLINE poly #-}

-- | Construct a polynomial with a given list of (degree, coeff) pairs
poly' :: (Eq p, Num p) => [(Int, p)] -> Poly p
poly' = foldl' setc nilpoly
{-# INLINE poly' #-}

-- | Empty polynomial
nilpoly :: Poly p
nilpoly = Poly mempty 0
{-# INLINE nilpoly #-}

-- | Set a coefficient of polynomial at a given degree
setc :: (Eq p, Num p) => Poly p -> (Int, p) -> Poly p
setc p@Poly {..} (i, x)
  | i < 0 = p
  | x == 0 = p
  | otherwise =
      p
        { coeff = M.insert i x coeff
        , deg = if i > deg then i else deg
        }
{-# INLINE setc #-}

-- | Get a coefficient of polynomial at a given degree
getc :: Num p => Poly p -> Int -> p
getc p i = case M.lookup i (coeff p) of
  Just x -> x
  _ -> 0
{-# INLINE getc #-}

-- | Get a coefficient of polynomial at the highest degree
atmostc :: Num p => Poly p -> p
atmostc p = getc p (deg p)

-- | Check if the coefficient at a given degree is nil
nilc :: Num p => Poly p -> Int -> Bool
nilc p i = case M.lookup i (coeff p) of
  Just _ -> False
  _ -> True
{-# INLINE nilc #-}

-- | Adjust and update degree of polynomial
update'deg :: (Eq p, Num p) => Poly p -> Int -> Poly p
update'deg p@Poly {} d
  | d < 1 = p {deg = 0}
  | getc p d /= 0 = p {deg = d}
  | otherwise = update'deg p (pred d)
{-# INLINE update'deg #-}

-- | Shift/unshift coefficients of polynomial (adjusting degrees)
shiftp :: (Eq p, Num p) => Poly p -> Int -> Poly p
shiftp Poly {..} n = poly' (first (+ n) <$> M.toList coeff)
{-# INLINE shiftp #-}

-- | Check if the coefficients of polynomial is empty
nil :: Poly p -> Bool
nil = M.null . coeff
{-# INLINE nil #-}

{- | Pairwise binary opteration with the same-degree zipped coefficients.
 This is different from 'zipWith' as this function plays with the longest one.
-}
zip'with :: (Eq p, Num p) => (p -> p -> p) -> Poly p -> Poly p -> Poly p
zip'with op f g =
  poly $
    uncurry op
      . (\d -> (getc f d, getc g d))
      <$> [0 .. max (deg f) (deg g)]
{-# INLINE zip'with #-}

-- | f(x) + g(x)
addpoly :: (Eq p, Num p) => Poly p -> Poly p -> Poly p
addpoly = zip'with (+)
{-# INLINE addpoly #-}

-- | f(x) - g(x)
subpoly :: (Eq p, Num p) => Poly p -> Poly p -> Poly p
subpoly = zip'with (-)
{-# INLINE subpoly #-}

-- | f(x) * g(x)
mulpoly :: (Eq p, Num p) => Poly p -> Poly p -> Poly p
mulpoly f g
  | nil f = nilpoly
  | nil g = nilpoly
  | otherwise =
      foldl'
        addpoly
        nilpoly
        [shiftp (scalepoly g . getc f $ d) d | d <- [0 .. deg f]]
{-# INLINE mulpoly #-}

-- | f(x) * k
scalepoly :: (Eq p, Num p) => Poly p -> p -> Poly p
scalepoly f@Poly {..} k
  | k == 0 = nilpoly
  | otherwise = update'deg (f {coeff = M.filter (/= 0) $ (k *) <$> coeff}) deg
{-# INLINE scalepoly #-}

-- | Infix operator for scalepoly
(|*) :: (Eq p, Num p) => Poly p -> p -> Poly p
(|*) = scalepoly
{-# INLINE (|*) #-}

{- | f(x) / g(x)
 Divide polynomials one another, then returns (quotient, remainder)
-}
divpoly :: (Eq p, Fractional p) => Poly p -> Poly p -> (Poly p, Poly p)
divpoly f g
  | nil g = throw DivideByZero
  | deg g == 0 = (f |* (1 / getc g 0), nilpoly)
  | deg f >= deg g = go nilpoly f g
  | otherwise = (nilpoly, f)
 where
  go q a b
    | deg a >= deg b =
        let n = deg a - deg b
            d = shiftp b n
            k = atmostc a / atmostc d
         in go (setc q (n, k)) (a - (d |* k)) b
    | otherwise =
        (q, a)
{-# INLINE divpoly #-}

-- | Infix divpoly
(|/) :: (Eq p, Fractional p) => Poly p -> Poly p -> (Poly p, Poly p)
(|/) = divpoly
{-# INLINE (|/) #-}

-- | f(x) ^ k: Integer exponentiation
powpoly :: (Eq p, Num p) => Poly p -> Integer -> Poly p
powpoly f k
  | k < 0 = die $ "Negative exponent: " ++ show k
  | k == 0 = poly [1]
  | k == 1 = f
  | even k = g * g
  | otherwise = f * (g * g)
 where
  g = powpoly f (div k 2)
{-# INLINE powpoly #-}

-- | f(x=x0): evaluate the polynomial at a given fixed x0
evalpoly :: (Eq p, Num p) => Poly p -> p -> p
evalpoly f x =
  foldl' (\acc c -> acc * x + c) 0 (getc f <$> [deg f, deg f - 1 .. 0])
{-# INLINE evalpoly #-}

-- | Infix evalpoly
(|=) :: (Eq p, Num p, Integral p) => Poly p -> p -> p
(|=) = evalpoly
{-# INLINE (|=) #-}
