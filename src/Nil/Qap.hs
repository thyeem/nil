{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

-- | Defines QAP (Quadratic Arithmetic Programs)
-- Based on https://eprint.iacr.org/2013/279.pdf
module Nil.Qap
  ( QAP (..),
    qap'from'r1cs,
    qap'from'circuit,
    qap'poly,
    qap'quot,
    validate'qap,
    R1CS (..),
    r1cs'from'circuit,
    validate'r1cs,
  )
where

import Control.DeepSeq (NFData)
import Control.Parallel
  ( par,
    pseq,
  )
import Data.List (transpose)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Poly
  ( lagrangepoly,
    (<.>),
    (<|.>),
    (|/),
  )
import Nil.Utils
  ( Pretty (..),
    pfold,
    (<%>),
  )

-- | Rank-1 Constraint System derived from Circuit
-- @
-- +--------+-------------------------------------------+
-- | r1cs'A | (d x [m+1]) matrix,                       |
-- | r1cs'B | representing structure of circuit         |
-- | r1cs'C |                                           |
-- +--------+-------------------------------------------+
-- | d      | Number of gates                           |
-- +--------+-------------------------------------------+
-- | m      | d + (# of instance) + (# of witness) + 1  |
-- +--------+-------------------------------------------+
-- | s      | [c0,..,c(m-1)], witness vector of size m  |
-- +--------+-------------------------------------------+
-- @
-- Each hold the constraint below:
-- <Ai . s> * <Bi . s> - <Ci . s> = 0, for i=[1..d]
data R1CS f = R1CS
  { r1cs'A :: [[f]],
    r1cs'B :: [[f]],
    r1cs'C :: [[f]],
    r1cs'num'inst :: Int
  }
  deriving (Eq, Show, Generic, NFData)

-- | Construct R1CS from Arithmetic Circuit
-- Language -> Lexemes -> AST -> 'Circuit' -> 'R1CS' -> QAP
r1cs'from'circuit :: (Num f, NFData f) => Circuit f -> R1CS f
r1cs'from'circuit circuit@Circuit {..} =
  r1cs'A `par`
    r1cs'B `par`
      r1cs'C `pseq`
        R1CS
          { r1cs'A,
            r1cs'B,
            r1cs'C,
            r1cs'num'inst = length c'pubs
          }
  where
    r1cs'A = l'from'gate (wire'keys circuit) <%> c'gates
    r1cs'B = r'from'gate (wire'keys circuit) <%> c'gates
    r1cs'C = o'from'gate (wire'keys circuit) <%> c'gates
{-# INLINE r1cs'from'circuit #-}

-- | Convert a given gate into a row-vector based on left-wire
l'from'gate :: (Num f) => [String] -> Gate f -> [f]
l'from'gate
  keys
  g@Gate
    { g'op = op,
      g'lwire = Wire lkey _ _ lval,
      g'rwire = Wire rkey _ _ rval
    } =
    [coeff key | key <- keys]
    where
      recip' = w'recip $ g'rwire g
      coeff key
        | recip' && key == const'key = 1
        | not recip' && op == Add && key == lkey && lkey == rkey = lval + rval
        | not recip' && op == Add && key == lkey = lval
        | not recip' && op == Add && key == rkey = rval
        | not recip' && op == Mul && key == lkey = lval
        | not recip' && op == End && key == lkey = lval
        | not recip' && op == End && key == rkey = rval
        | not recip' && op `notElem` [Mul, Add, End] && key == const'key = 1
        | otherwise = 0
{-# INLINE l'from'gate #-}

-- | Convert a given gate into a row-vector based on right-wire
r'from'gate :: (Num f) => [String] -> Gate f -> [f]
r'from'gate
  keys
  g@Gate
    { g'op = op,
      g'rwire = Wire rkey _ _ rval,
      g'owire = Wire okey _ _ oval
    } =
    [coeff key | key <- keys]
    where
      recip' = w'recip $ g'rwire g
      coeff key
        | recip' && key == okey = oval
        | not recip' && op == Add && key == const'key = 1
        | not recip' && op == Mul && key == rkey = rval
        | not recip' && op == End && key == const'key = 1
        | not recip' && op `notElem` [Mul, Add, End] && key == okey = oval
        | otherwise = 0
{-# INLINE r'from'gate #-}

-- | Convert a given gate into a row-vector based on out-wire
o'from'gate :: (Num f) => [String] -> Gate f -> [f]
o'from'gate keys Gate {g'op = op, g'owire = Wire okey _ _ oval} = [coeff key | key <- keys]
  where
    coeff key
      | op == End && key == okey = 2
      | op /= End && key == okey = oval
      | otherwise = 0
{-# INLINE o'from'gate #-}

-- | Check if R1CS constraints hold for a given witness vector v:
-- (r1cs'A . v) * (r1cs'B . v) - (r1cs'C . v) ==? 0
--
-- Complied with the rules, this will be automatically satisfied.
validate'r1cs :: (Eq f, Num f, Monoid f, NFData f) => R1CS f -> [f] -> Bool
validate'r1cs R1CS {..} v = all (== 0) $ f <$> zip3 r1cs'A r1cs'B r1cs'C
  where
    f (a, b, c) = (a <.> v) * (b <.> v) - (c <.> v)
{-# INLINE validate'r1cs #-}

instance (Integral f, Show f) => Pretty (R1CS f)

-- | QAP (Quadratic Arithmetic Programs)
-- @
-- +------+--------------------------------------+-----------------------------+
-- | QAP  | Q := (V, W, Y, t(x))                 |                             |
-- |------+--------------------------------------+-----------------------------|
-- | V    | [ Vi(x) ] = [ V0(x), .., Vm-1(x) ]   | dim of (m x [d+1]) matrix   |
-- |------+--------------------------------------+-----------------------------|
-- | W    | [ Wi(x) ] = [ W0(x), .., Wm-1(x) ]   | dim of (m x [d+1]) matrix   |
-- |------+--------------------------------------+-----------------------------|
-- | Y    | [ Yi(x) ] = [ Y0(x), .., Ym-1(x) ]   | dim of (m x [d+1]) matrix   |
-- |------+--------------------------------------+-----------------------------|
-- | t(x) | (x-1)(x-2)...(x-d)                   | max. d-degree poly          |
-- |------+--------------------------------------+-----------------------------|
-- | p(x) | (V . s) * (W . s)  - (Y . s)         | max. 2*(d-1)-degree poly    |
-- |------+--------------------------------------+-----------------------------|
-- | h(x) | p(x) == h(x) * t(x), qap quotient    | max. (d-2)-degree poly      |
-- |------+--------------------------------------+-----------------------------|
-- | w    | [c0,...,c(m-1)], qap witness         | m-degree vector             |
-- |------+--------------------------------------+-----------------------------|
-- | d    | # of gates                           |                             |
-- |------+--------------------------------------+-----------------------------|
-- | m    | d + #instances + #witnesses + 1      |                             |
-- +------+--------------------------------------+-----------------------------+
-- @
data QAP f = QAP
  { qap'V :: [[f]],
    qap'W :: [[f]],
    qap'Y :: [[f]],
    qap't :: [f],
    qap'num'inst :: Int
  }
  deriving (Eq, Show, Generic, NFData)

-- | Construct QAP from R1CS
-- Language -> Lexeme -> AST -> Circuit -> R1CS -> [QAP]
qap'from'r1cs :: (Eq f, Fractional f, Enum f, NFData f) => R1CS f -> QAP f
qap'from'r1cs R1CS {..} =
  qap'V `par`
    qap'W `par`
      qap'Y `par`
        qap't `pseq`
          QAP
            { qap'V,
              qap'W,
              qap'Y,
              qap't,
              qap'num'inst = r1cs'num'inst
            }
  where
    qap'V = lagrangepoly . zip d <%> transpose r1cs'A
    qap'W = lagrangepoly . zip d <%> transpose r1cs'B
    qap'Y = lagrangepoly . zip d <%> transpose r1cs'C
    qap't = pfold (*) (([0, 1] -) . (: []) <%> d)
    d = [1 .. fromIntegral . length $ r1cs'A]
{-# INLINEABLE qap'from'r1cs #-}

-- | Derive QAP from Circuit
qap'from'circuit ::
  (Eq f, Fractional f, Enum f, NFData f) => Circuit f -> QAP f
qap'from'circuit = qap'from'r1cs . r1cs'from'circuit
{-# INLINE qap'from'circuit #-}

-- | p(x), p(x) == (V . s) * (W . s)  - (Y . s)
qap'poly :: (Eq f, Fractional f, NFData f) => QAP f -> [f] -> [f]
qap'poly qap vec'wit =
  (qap'V qap <|.> vec'wit) * (qap'W qap <|.> vec'wit) - (qap'Y qap <|.> vec'wit)
{-# INLINE qap'poly #-}

-- | h(x), p(x) == h(x) * t(x)
qap'quot :: (Eq f, Fractional f, NFData f) => QAP f -> [f] -> [f]
qap'quot qap vec'wit = qap'poly qap vec'wit / qap't qap
{-# INLINE qap'quot #-}

-- | Validate QAP
-- Check if t(x) | p(x) or exists h(x) such that p(x) == h(x) * t(x)
validate'qap :: (Eq f, Fractional f, NFData f) => QAP f -> [f] -> Bool
validate'qap qap vec'wit = null . snd $ qap'poly qap vec'wit |/ qap't qap
{-# INLINE validate'qap #-}

instance (Integral f, Show f) => Pretty (QAP f)
