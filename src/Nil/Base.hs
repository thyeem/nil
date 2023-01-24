module Nil.Base where

import Control.Monad (zipWithM)
import Data.Bits (Bits (..))
import Data.List (find)
import Data.Maybe (fromMaybe)
import Nil.Utils (die)

{- | Reciprocal in Z/pZ
 * By Fermat's little theorem: a^(p-1) = 1 (mod p),
   1 / a = a^(-1) = a^(p-2) (mod p)

 * By Euclidean algorithm: egcd(a, p) -> (x, y)
   x = a^(-1)  (can be negative, but the same in modular arithmetic)
-}
(~%) :: Integral a => a -> a -> a
-- a ~% p = modpow a (p - 2) p
a ~% p = fst $ egcd a p
{-# INLINE (~%) #-}

infixl 9 ~%

{- | Extended Euclidean algorithm based on Bezout's identity
 ax + by = gcd(a, b), returns (x, y)
-}
egcd :: Integral a => a -> a -> (a, a)
egcd _ 0 = (1, 0)
egcd a b = (y, x - q * y)
 where
  (q, r) = quotRem a b
  (x, y) = egcd b r

{- | Solve a given system of congruences using Chinese Remainder Theorem (CRT).
 [(Int, Int)]
 =: [(eq.1 residue, eq.1 modulo), (eq.2 residue, eq.2 modulo),..]
-}
chineseRemainder :: Integral a => [(a, a)] -> Maybe a
chineseRemainder congruences =
  (`mod` _N)
    . sum
    . hadamard _Ni
    . hadamard residues
    <$> zipWithM getMi _Ni moduli
 where
  (residues, moduli) = unzip congruences
  _N = product moduli
  _Ni = (_N `div`) <$> moduli
  hadamard = zipWith (*)
  getMi a p
    | (a * inv) ~% p == 1 = Just inv
    | otherwise = Nothing
   where
    inv = a ~% p

-- | Modular power with base, exponent, and modulo
modpow :: (Bits a, Integral a, Show a) => a -> a -> a -> a
modpow b e m
  | m <= 0 = die $ "non-positive modulo used: " ++ show m
  | e < 0 = die $ "negative exponent used: " ++ show e
  | e == 0 = 1
  | otherwise = t * modpow ((b * b) `mod` m) (shiftR e 1) m `mod` m
 where
  t = if testBit e 0 then b `mod` m else 1

-- | Prime numbers (unbounded, endless sieving from 2)
primes :: Integral a => [a]
primes = 2 : sieve primes [3 ..]
 where
  sieve (p : ps) xs = q <> sieve ps [x | x <- t, rem x p > 0]
   where
    (q, t) = span (< p * p) xs
  sieve _ _ = die "unreachable. broken function: primes"

-- | Prime factorization
primefactors :: (Integral a, Show a) => a -> [a]
primefactors n
  | n > 1 = go n primes
  | otherwise = die $ "not positive integer greater than 2: " ++ show n
 where
  go n' primes' = case primes' of
    p : ps
      | p * p > n' -> [n']
      | rem n' p == 0 -> p : go (quot n' p) primes'
      | otherwise -> go n' ps
    _ -> die "unreachable. broken function: primefactors"

-- | Primality test based on prime factorization (reliable, but slow)
primep :: (Integral a, Show a) => a -> Bool
primep n = primefactors n == [n]

{- | Primality test using Fermat's probable prime (quick, but not perfect)
 consider Miller-Rabin and Baillie-PSW (Fermat + Lucas)
-}
primep'fermat :: (Bits a, Integral a, Show a) => a -> a -> Bool
primep'fermat b n
  | n < 0 = die "Negative argument"
  | n == 1 = False
  | n == 2 = True
  | otherwise = modpow b n n == b

{- | Euler's criterion (or Legendre Symbol)
 (a | p) =  1 (mod p) if a is quadratic residue [a =: x^2 && a /= 0  (mod p)]
         = -1 (mod p) if a is non-quadratic residue
         =  0 (mod p) if a =: 0  (mod p)
-}
eulerCriterion :: (Bits a, Integral a, Show a) => a -> a -> a
eulerCriterion a p = modpow a ((p - 1) `div` 2) p

{- | Check if a given field element is quadratic residue or not
 'aRp' is the notation Gauss used for quadratic residues
-}
aRp :: (Bits a, Integral a, Show a) => a -> a -> Bool
aRp a p = eulerCriterion a p == 1

{- | Check if a given field element is quadratic non-residue or not
 'aNp' is the notation Gauss used for quadratic residues
-}
aNp :: (Bits a, Integral a, Show a) => a -> a -> Bool
aNp a p = eulerCriterion a p == p - 1

-- | Find Q and S such that p-1 = Q * 2^S (with odd Q) by factoring out power of 2
factorQ2S :: (Bits a, Integral a) => a -> (a, a)
factorQ2S p = go (p - 1, 0)
 where
  go (q, s)
    | testBit q 0 = (q, s)
    | otherwise = go (shiftR q 1, s + 1)

-- | Find any number 'z' has no square root (non-qaudratic residue) in [1,p)"""
findz :: (Bits a, Integral a, Show a) => a -> Maybe a
findz p = find (`aNp` p) [1 .. p - 1]

{- | Find sqrt(n) over Z/pZ based on Tonelli-Shanks
 'p' is a odd prime (p is a prime and p /= 2)

 Algorithm:
 1. Factorize (p-1) out power of two:  p-1 = Q * 2^S
 2. Search for a non-quadratic residue, z in Z/pZ
 3. Set M <- S, c <- z^Q, t <- n^Q, R <- n^((Q+1)/2)
 4. Loop: (as shown below)
   - if t=0, return 0
   - if t=1, return R
   - otherwise, find the least i such that t^(2^i) = 1 for [1, M)
     b = c^(2^(M-i-1))
   - set the below and repeat
     M <- i, c <- b^2, t <- t*b^2, R <- R*b
-}
sqrt'zpz :: (Bits a, Integral a, Show a) => a -> a -> Maybe a
sqrt'zpz n p
  | n == 0 =
      Just 0
  | aNp n p =
      Nothing
  | otherwise =
      let (_Q, _S) = factorQ2S p
       in case findz p of
            Just z ->
              loop
                _S
                (modpow z _Q p)
                (modpow n _Q p)
                (modpow n ((_Q + 1) `div` 2) p)
            _ -> die . unwords $ ["not found sqrt of ", show n, "over", show p]
 where
  loop _M c t _R
    | t == 0 =
        Just 0
    | t == 1 =
        Just _R
    | otherwise =
        let i =
              die ("cannot find proper i from t: " ++ show t)
                `fromMaybe` find (\x -> modpow t (2 ^ x) p == 1) [1 .. _M - 1]
            b = modpow c (modpow 2 (_M - i - 1) p) p
         in loop i ((b * b) `mod` p) ((t * b * b) `mod` p) ((_R * b) `mod` p)
