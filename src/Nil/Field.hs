{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Nil.Field
  ( Field(..)
  , Primefield(..)
  , pf
  , unpf
  , Extensionfield(..)
  , ef
  , unef
  , unip
  , Irreduciblepoly(..)
  ) where

import           Control.DeepSeq ( NFData )

import           Data.Aeson      ( FromJSON, ToJSON )
import           Data.Bifunctor  ( first )
import           Data.Ratio      ( (%) )
import           Data.Store      ( Store )

import           GHC.Generics    ( Generic )
import           GHC.TypeLits    ( KnownNat, Nat, natVal )

import           Nil.Base        ( (~%) )
import           Nil.Poly        ( egcdpoly, (|*), (|/) )
import           Nil.Utils       ( Pretty (..), die )

import           System.Random   ( Random (..) )

import           Test.QuickCheck ( Arbitrary (..), choose )

-- | Kind for Galois field or Finite field, GF(q) or GF(p^k)
class (Eq k, Ord k, Fractional k, NFData k, Show k, Pretty k) =>
      Field k
  -- | Characteristic @p@ of the field
  where
  char :: k -> Integer
  -- | Degree of field
  deg :: k -> Integer
  -- | i-th power of Frobenius endomorphism @x -> x^(q^i)@
  frob :: k -> Integer -> k
  -- | Multiplicative identity of the field
  one :: k -> k
  -- | Additive identity of the field
  zero :: k -> k
  zero f = one f - one f
  -- | Order or cardinality of the field -> @p^k@
  order :: k -> Integer
  order = (^) <$> char <*> deg
  {-# MINIMAL char, deg, frob, one #-}

-- | Primefield GF(p^k, k=1) or Z/pZ (integers modulo p)
newtype Primefield (p :: Nat) =
  P Integer
  deriving (Eq, Ord, Generic, NFData, Store, ToJSON, FromJSON)

-- | Construct Primefield p
--
-- > 7 :: Primefield 13
-- `7
--
-- > type F = Primefield 1009
-- > 12345 + 54321 :: F
-- `72
pf :: (KnownNat p) => Integer -> Primefield p
pf n = f
  where
    f = P $ n `mod` char f

{-# INLINEABLE pf #-}
unpf :: (KnownNat p) => Primefield p -> Integer
unpf (P n) = n

{-# INLINEABLE unpf #-}
instance (KnownNat p) => Field (Primefield p) where
  char = natVal
  {-# INLINE char #-}
  deg = const 1
  {-# INLINE deg #-}
  frob = const
  {-# INLINE frob #-}
  one = const 1
  {-# INLINE one #-}

instance (KnownNat p) => Monoid (Primefield p) where
  mempty = 1

instance (KnownNat p) => Semigroup (Primefield p) where
  (<>) = (*)

instance (KnownNat p) => Num (Primefield p) where
  (P !a) + (P !b) = pf $ a + b
  {-# INLINE (+) #-}
  (P !a) - (P !b) = pf $ a - b
  {-# INLINE (-) #-}
  (P !a) * (P !b) = pf $ a * b
  {-# INLINE (*) #-}
  negate (P !a) = pf $ negate a
  {-# INLINE negate #-}
  fromInteger = pf
  signum _ = 1
  abs = id

instance (KnownNat p) => Fractional (Primefield p) where
  recip x@(P !a) = pf $ a ~% p
    where
      p = char x
  {-# INLINE recip #-}
  (/) !a !b = a * recip b
  {-# INLINE (/) #-}
  fromRational = undefined

instance (KnownNat p) => Integral (Primefield p) where
  toInteger = unpf
  {-# INLINE toInteger #-}
  quotRem (P !a) (P !b) = (pf $ quot a b, pf $ rem a b)
  {-# INLINE quotRem #-}

instance (KnownNat p) => Real (Primefield p) where
  toRational f = toInteger f % 1

instance (KnownNat p) => Random (Primefield p) where
  random = randomR (minBound, maxBound)
  {-# INLINE random #-}
  randomR (a, b) = first fromInteger . randomR (toInteger a, toInteger b)
  {-# INLINE randomR #-}

instance (KnownNat p) => Arbitrary (Primefield p) where
  arbitrary = choose (minBound, maxBound)
  {-# INLINE arbitrary #-}

instance (KnownNat p) => Bounded (Primefield p) where
  minBound = pf 0
  {-# INLINE minBound #-}
  maxBound = minBound - 1
  {-# INLINE maxBound #-}

instance (KnownNat p) => Enum (Primefield p) where
  succ = (+ 1)
  {-# INLINE succ #-}
  pred = flip (-) 1
  {-# INLINE pred #-}
  toEnum = fromIntegral
  {-# INLINE toEnum #-}
  fromEnum = fromInteger . toInteger
  {-# INLINE fromEnum #-}

-- | Extension field, GF(p^k, k > 1)
--
--  F = Prime Field of characteristic p (base field)
--  F[x] = polynomial f(x) of field F coefficient
--  p(x) = irreducible monic polynomial of F[x] over F
--  Quotient ring, F[x] / p(x) -> Extension Field!
--  +----+--------------------------------------------------------------------+
--  | p  | characteristic of field                                            |
--  +----+--------------------------------------------------------------------+
--  | k  | degree of field (Prime Field if k=1, Extension Field when k>1)     |
--  +----+--------------------------------------------------------------------+
--  | q  | degree of field (p ** q)                                           |
--  +----+--------------------------------------------------------------------+
--  | fX | polynomial f[X] over p in Extension-Field construction             |
--  +----+--------------------------------------------------------------------+
--  | pX | irreducible polynomial p(x) over p in Extension-Field construction |
--  +----+--------------------------------------------------------------------+
data Extensionfield f i =
  E (Irreduciblepoly f i) [f]
  deriving (Eq, Ord, Generic, NFData)

-- Irreducible polynomial over primefield f
newtype Irreduciblepoly f i =
  I [f]
  deriving (Eq, Ord, Generic, NFData)

-- | Construct Extensionfield f i
--
-- > ip = I [1,0,1 :: Primefield 13]
-- > ef ip [111,222,333,444,555]
-- E (I [`1,`0,`1]) [`8,`12]
ef :: (Eq f, Fractional f, Field f) => [f] -> [f] -> Extensionfield f i
ef px fx = E (I px) fx'
  where
    (_, fx') = fx |/ px

{-# INLINEABLE ef #-}
unef :: (Eq f, Fractional f, Field f) => Extensionfield f i -> [f]
unef (E _ fx) = fx

{-# INLINEABLE unef #-}
unip :: (Eq f, Fractional f, Field f) => Extensionfield f i -> [f]
unip (E (I px) _) = px

{-# INLINEABLE unip #-}
instance (Field f) => Semigroup (Extensionfield f i) where
  (<>) = (*)

instance (Field f) => Monoid (Extensionfield f i) where
  mempty = f
    where
      f = one f

instance (Field f) => Field (Extensionfield f i) where
  char = const $ char (1 :: f)
  {-# INLINE char #-}
  deg (E (I p) _) = fromIntegral $ length p - 1
  {-# INLINE deg #-}
  frob x = (x ^) . (p ^)
    where
      p = char x
  {-# INLINE frob #-}
  one (E p _) = E p [1]
  {-# INLINE one #-}

instance (Field f) => Num (Extensionfield f i) where
  E (I !p) !fx + E _ !gx = ef p (fx + gx)
  {-# INLINE (+) #-}
  E (I !p) !fx - E _ !gx = ef p (fx - gx)
  {-# INLINE (-) #-}
  E (I !p) !fx * E _ !gx = ef p (fx * gx)
  {-# INLINE (*) #-}
  negate (E !p !fx) = E p (negate fx)
  {-# INLINE negate #-}
  fromInteger = undefined
  signum _ = undefined
  abs = undefined

instance (Field f) => Fractional (Extensionfield f i) where
  fromRational = undefined
  (/) !a !b = a * recip b
  {-# INLINE (/) #-}
  recip (E (I !px) !fx) = ef px (x |* recip g)
    where
      (x, y) = egcdpoly fx px
      g = head $ fx * x + px * y
  {-# INLINE recip #-}

instance (KnownNat p) => Show (Primefield p) where
  showsPrec n p = showString "`" . showsPrec n (unpf p)

instance (KnownNat p) => Read (Primefield p) where
  readsPrec n ('`':s) = [(pf a, s') | (a, s') <- readsPrec n s]
  readsPrec _ a       = die $ "Failed to read a Primefield element: " ++ a

instance (KnownNat p) => Pretty (Primefield p) where
  pretty = show

instance (Show f, Field f) => Show (Extensionfield f i) where
  show = show . unef

instance (Show f, Field f) => Pretty (Extensionfield f i) where
  pretty = pretty . unef

instance (Show f) => Show (Irreduciblepoly f i) where
  show (I ip) = show ip

instance (Show f) => Pretty (Irreduciblepoly f i) where
  pretty (I ip) = pretty ip
