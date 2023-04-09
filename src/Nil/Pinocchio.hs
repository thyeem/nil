{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Nil.Pinocchio where

-- ( EvaluationKey(..)
-- , VerificationKey(..)
-- , Proof(..)
-- , ToxicWastes
-- , Fr
-- , toxicwaste
-- , compile'language
-- , zksetup
-- , zkprove
-- , zkverify
-- , zktest
-- , decode'file
-- ) where

import Control.DeepSeq (NFData)
import Control.Monad (when)
import Control.Parallel (par, pseq)
import qualified Data.Aeson as J
import Data.Bifunctor (second)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import Data.Either (fromRight)
import Data.Functor ((<&>))
import Data.Map (Map, toList)
import Data.Proxy
import Data.Store (PeekException (..), Store, decode)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Curve (Curve, Point, c'g, toA, (<~*>), (~*))
import Nil.Ecdata (BN254, BN254'G2, BN254'GT, Fr, G1, G2, bn254'g1, bn254'gt, g1, g2)
import Nil.Eval (statement, vec'fromWmap, wire'vals, wmap'fromList)
import Nil.Lexer (tokenize)
import Nil.Pairing (pairing)
import Nil.Parser (parse)
import Nil.Poly ((|=))
import Nil.Qap (QAP (..), qap'from'circuit, qap'quot)
import Nil.Utils
  ( Pretty (..),
    bytes'from'str,
    die,
    info'io,
    int'from'bytes,
    int'from'str,
    ranf,
    slice,
    stderr,
    (<%>),
    (|&|),
    (|*|),
    (|+|),
    (|/|),
    (|=|),
  )
import Text.Read (readMaybe)

-- | zk-SNARKs based on Pinocchio protocol (https://eprint.iacr.org/2013/279.pdf)
-- @
-- +-----------+----------------------------------------------------+--------+
-- | CRS       | Common Reference String:                           | randos |
-- |           | { s, alpha, beta-v beta-w, beta-y, gamma }         |        |
-- +-----------+----------------------------------------------------+--------+
-- | d         | # of gates                                         | value  |
-- +-----------+----------------------------------------------------+--------+
-- | n         | # of instances                                     | value  |
-- +-----------+----------------------------------------------------+--------+
-- | m         | d + n + (# of witness) + 1                         | value  |
-- +-----------+----------------------------------------------------+--------+
-- | w         | [c0,c1,..,c[m-1]], qap witness of (m-1)-degree     | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | s^i       | [s^0,s^1,..,s^d], (d-degree), s from CRS           | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | V, W, Y   | dim of (m x d) matrices from QAP                   |        |
-- +-----------+----------------------------------------------------+--------+
-- | V0        | V[0], 0-th vector of qap'V                         | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | Vio       | V[1:n], slice of qap'V (instances)                 | matrix |
-- +-----------+----------------------------------------------------+--------+
-- | Vj        | V[n+1:m-1], slice of qap'V (witnesses)             | matrix |
-- +-----------+----------------------------------------------------+--------+
-- | V0(s)     | eval V0 at s                                       | value  |
-- +-----------+----------------------------------------------------+--------+
-- | Vj(s)     | eval each row polynomial of V[n+1:m-1] at s        | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | Wk(s)     | eval each row polynomial of W[1:n] at s            | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | Yk(s)     | the same as Wk(s)                                  | poly   |
-- +-----------+----------------------------------------------------+--------+
-- | V(s)      | Hadamart procut of V and w, eval at s and fold.    | value  |
-- |           | or inner product of Vk(s) and w:                   |        |
-- |           | V(s) = c0 * V0(s) + .. + cm * Vm-1(s)              |        |
-- +-----------+----------------------------------------------------+--------+
-- | W(s),Y(s) | the same as V(s)                                   | value  |
-- +-----------+----------------------------------------------------+--------+
-- | Vio(s)    | Vio(s) = c1 * V1(s) + .. + cn * Vn(s)              | value  |
-- +-----------+----------------------------------------------------+--------+
-- | Vj(s)     | Vj(s) = c[n+1] * V[n+1] + .. + c[m-1] * Vm-1(s)    | value  |
-- +-----------+----------------------------------------------------+--------+
-- | E(k)      | homomorphic encryption, k*G = G + .. + G (k-times) |        |
-- +-----------+----------------------------------------------------+--------+
-- | G         | predefined base point on an elliptic curve         |        |
-- +-----------+----------------------------------------------------+--------+
-- | E(V(s))   | E(V0(s)) + E(Vio(s)) + E(Vj(s) == E(V(s))          | point  |
-- +-----------+----------------------------------------------------+--------+
-- | E(W(s))   | E(W0(s)) + E(W(s)) == E(W(s))                      | point  |
-- +-----------+----------------------------------------------------+--------+
-- | E(Y(s))   | E(Y0(s)) + E(Y(s)) == E(Y(s))                      | point  |
-- +-----------+----------------------------------------------------+--------+
-- | E(s^i)    | E(0) + E(s) + .. + E(s^d)                          | point  |
-- +-----------+----------------------------------------------------+--------+
-- @

-- | Evaluation Key or Proving key
data EvaluationKey = EKey
  { eEvj :: [Point BN254 G1], -- [ E(Vj(s)) ]
    eEwk :: [Point BN254 G1], -- [ E(Wk(s)) ]
    eE'wk :: [Point BN254'G2 G2], -- [ E'(Wk(s)) ]
    eEyk :: [Point BN254 G1], -- [ E(Yk(s)) ]
    eEavj :: [Point BN254 G1], -- [ E(a * Vj(s)) ]
    eEawk :: [Point BN254 G1], -- [ E(a * Wk(s)) ]
    eEayk :: [Point BN254 G1], -- [ E(a * Yk(s)) ]
    eEbvvj :: [Point BN254 G1], -- [ E(bv * Vj(s)) ]
    eEbwwk :: [Point BN254 G1], -- [ E(bw * Wk(s)) ]
    eEbyyk :: [Point BN254 G1], -- [ E(by * Yk(s)) ]
    eEsi :: [Point BN254 G1], -- [ E(s^i) ]
    eEasi :: [Point BN254 G1] -- [ E(a * s^i) ]
  }
  deriving (Eq, Show, Generic, NFData)

-- | Verification Key
data VerificationKey = VKey
  { vE1 :: Point BN254'G2 G2, -- E(1)
    vEa :: Point BN254'G2 G2, -- E(a)
    vEr :: Point BN254'G2 G2, -- E(r)
    vErbv :: Point BN254'G2 G2, -- E(r * bv)
    vErbw :: Point BN254'G2 G2, -- E(r * bw)
    vErby :: Point BN254'G2 G2, -- E(r * by)
    vEt :: Point BN254'G2 G2, -- E(t(s))
    vEv0 :: Point BN254 G1, -- E(V0(s))
    vEw0 :: Point BN254'G2 G2, -- E(W0(s))
    vEy0 :: Point BN254 G1, -- E(Y0(s))
    vEvio :: [Point BN254 G1] -- [ E(Vio(s)) ]
  }
  deriving (Eq, Show, Generic, NFData)

-- | Proof
data Proof = Proof
  { pEvJ :: Point BN254 G1, -- E(Vj(s))
    pEw :: Point BN254 G1, -- E(W(s))
    pE'w :: Point BN254'G2 G2, -- E'(W(s))
    pEy :: Point BN254 G1, -- E(Y(s))
    pEh :: Point BN254 G1, -- E(h(s))
    pEavJ :: Point BN254 G1, -- E(a * Vj(s))
    pEaw :: Point BN254 G1, -- E(a * W(s))
    pEay :: Point BN254 G1, -- E(a * Y(s))
    pEah :: Point BN254 G1, -- E(a * h(s))
    pEbvwy :: Point BN254 G1 -- E(bv * V(s) + bw * W(s) + by * Y(s))
  }
  deriving (Eq, Show, Generic, NFData)

-- | Set of random numbers used during setup phase
type ToxicWastes = (Fr, Fr, Fr, Fr, Fr, Fr)

deriving instance Pretty ToxicWastes

deriving instance Store EvaluationKey

deriving instance Store VerificationKey

deriving instance Store Proof

-- | Generate random set (s, alpha, beta-v, beta-w, beta-y, gamma)
-- MUST be immediately destroyed right after a ceremony
toxicwaste :: IO ToxicWastes
toxicwaste = do
  s <- ranf
  a <- ranf
  bv <- ranf
  bw <- ranf
  by <- ranf
  r <- ranf
  pure (s, a, bv, bw, by, r)
{-# INLINE toxicwaste #-}

-- | Default elliptic curve of this protocol
def'curve :: Curve BN254 G1
def'curve = bn254'g1

-- | Generate evaluation key and verification key from the given CRS and QAP
zksetup :: QAP Fr -> ToxicWastes -> (EvaluationKey, VerificationKey)
zksetup QAP {..} (s, a, bv, bw, by, r) = ekey `par` vkey `pseq` (ekey, vkey)
  where
    ekey =
      eEvj `par`
        eEwk `par`
          eE'wk `par`
            eEyk `par`
              eEavj `par`
                eEawk `par`
                  eEayk `par`
                    eEbvvj `par`
                      eEbwwk `par`
                        eEbyyk `par`
                          eEsi `par`
                            eEasi `pseq`
                              EKey
                                { eEvj,
                                  eEwk,
                                  eE'wk,
                                  eEyk,
                                  eEavj,
                                  eEawk,
                                  eEayk,
                                  eEbvvj,
                                  eEbwwk,
                                  eEbyyk,
                                  eEsi,
                                  eEasi
                                }

    vkey =
      vE1 `par`
        vEa `par`
          vEr `par`
            vErbv `par`
              vErbw `par`
                vErby `par`
                  vEt `par`
                    vEv0 `par`
                      vEw0 `par`
                        vEy0 `par`
                          vEvio `pseq`
                            VKey
                              { vE1,
                                vEa,
                                vEr,
                                vErbv,
                                vErbw,
                                vErby,
                                vEt,
                                vEv0,
                                vEw0,
                                vEy0,
                                vEvio
                              }

    eEvj = lift'G1 <%> vj -- [ E(Vj(s)) ]
    eEwk = lift'G1 <%> wk -- [ E(Wk(s)) ]
    eE'wk = lift'G2 <%> wk -- [ E'(Wk(s)) ]
    eEyk = lift'G1 <%> yk -- [ E(Yk(s)) ]
    eEavj = lift'G1 . (a *) <%> vj -- [ E(a * Vj(s)) ]
    eEawk = lift'G1 . (a *) <%> wk -- [ E(a * Wk(s)) ]
    eEayk = lift'G1 . (a *) <%> yk -- [ E(a * Yk(s)) ]
    eEbvvj = lift'G1 . (bv *) <%> vj -- [ E(bv * Vj(s)) ]
    eEbwwk = lift'G1 . (bw *) <%> wk -- [ E(bw * Wk(s)) ]
    eEbyyk = lift'G1 . (by *) <%> yk -- [ E(by * Yk(s)) ]
    eEsi = lift'G1 <%> si -- [ E(s^i) ]
    eEasi = lift'G1 . (a *) <%> si -- [ E(a * s^i) ]
    vE1 = lift'G2 1 -- E(1)
    vEa = lift'G2 a -- E(a)
    vEr = lift'G2 r -- E(r)
    vErbv = lift'G2 (r * bv) -- E(r * bv)
    vErbw = lift'G2 (r * bw) -- E(r * bw)
    vErby = lift'G2 (r * by) -- E(r * by)
    vEt = lift'G2 t -- E(t(s))
    vEv0 = lift'G1 v0 -- E(V0(s))
    vEw0 = lift'G2 w0 -- E(W0(s))
    vEy0 = lift'G1 y0 -- E(Y0(s))
    vEvio = lift'G1 <%> vio -- [ E(Vio(s)) ]
    lift'G1 = toA . (g1 ~*) -- lift a scalar to a point on G1
    lift'G2 = toA . (g2 ~*) -- lift a scalar to a point on G2
    vio = (|= s) . (qap'V !!) <%> [1 .. n] -- [ Vio(s) ]
    vj = (|= s) . (qap'V !!) <%> [n + 1 .. m - 1] -- [ Vj(s) ]
    wk = (|= s) . (qap'W !!) <%> [1 .. m - 1] -- [ Wk(s) ]
    yk = (|= s) . (qap'Y !!) <%> [1 .. m - 1] -- [ Yk(s) ]
    v0 = (|= s) . head $ qap'V -- V0(s)
    w0 = (|= s) . head $ qap'W -- W0(s)
    y0 = (|= s) . head $ qap'Y -- Y0(s)
    si = (s ^) <%> [0 .. d] -- [ s^i ]
    t = qap't |= s -- t(s)
    n = qap'num'inst -- # of instance
    m = length qap'V -- 1 + n + (# of witness) + d
    d = length (head qap'V) -- # of gates
{-# INLINEABLE zksetup #-}

-- | Generate zkproof
zkprove :: QAP Fr -> EvaluationKey -> [Fr] -> Proof
zkprove qap@QAP {..} EKey {..} witness = proof
  where
    proof =
      pEvJ `par`
        pEw `par`
          pE'w `par`
            pEy `par`
              pEh `par`
                pEavJ `par`
                  pEaw `par`
                    pEay `par`
                      pEah `par`
                        pEbvwy `pseq`
                          Proof
                            { pEvJ,
                              pEw,
                              pE'w,
                              pEy,
                              pEh,
                              pEavJ,
                              pEaw,
                              pEay,
                              pEah,
                              pEbvwy
                            }

    pEvJ = toA $ eEvj <~*> witJ -- E(Vj(s))
    pEw = toA $ eEwk <~*> witK -- E(W(s))
    pE'w = toA $ eE'wk <~*> witK -- E'(W(s))
    pEy = toA $ eEyk <~*> witK -- E(Y(s))
    pEh = toA $ eEsi <~*> h -- E(h(s))
    pEavJ = toA $ eEavj <~*> witJ -- E(a * Vj(s))
    pEaw = toA $ eEawk <~*> witK -- E(a * W(s))
    pEay = toA $ eEayk <~*> witK -- E(a * Y(s))
    pEah = toA $ eEasi <~*> h -- E(a * h(s))
    pEbvwy =
      toA $
        (eEbvvj <~*> witJ)
          |+| (eEbwwk <~*> witK)
          |+| (eEbyyk <~*> witK) -- E(bv * Vj(s) + bw * W(s) + by * Y(s))
    h = qap'quot qap witness -- h(x)
    n = qap'num'inst -- number of instances
    m = length qap'V -- 1 + n + (# of witness) + d
    witJ = witness `slice` (n + 1, m - 1) -- witness[n+1:]
    witK = witness `slice` (1, m - 1) -- witness[1:]
{-# INLINEABLE zkprove #-}

-- | Verify the given zkproof
zkverify :: Proof -> VerificationKey -> [Fr] -> Bool
zkverify Proof {..} VKey {..} instances = checkA |&| checkB |&| checkD
  where
    -- checkA: check alpha-term proof (8-pairings)
    -- e( E(Vj(s)), E(a) ) == e( E(a * Vj(s)), E(1) )
    -- e( E(W(s)),  E(a) ) == e( E(a * W(s)),  E(1) )
    -- e( E(Y(s)),  E(a) ) == e( E(a * Y(s)),  E(1) )
    -- e( E(h(s)),  E(a) ) == e( E(a * h(s)),  E(1) )
    checkA =
      (e pEvJ vEa |=| e pEavJ vE1)
        |&| (e pEw vEa |=| e pEaw vE1)
        |&| (e pEy vEa |=| e pEay vE1)
        |&| (e pEh vEa |=| e pEah vE1)

    -- checkB: check beta-term proof (4-pairings)
    -- e( E(bv * Vj(s) + bw * W(s) + by * Y(s)), E(r) )
    -- == [ e( E(Vj(s)), E(r * bv) )
    --    * e( E(W(s)),  E(r * bw) )
    --    * e( E(Y(s)),  E(r * by) ) ]
    checkB =
      e pEbvwy vEr |=| (e pEvJ vErbv |*| e pEw vErbw |*| e pEy vErby)

    -- checkD: check QAP divisibility (3-pairings)
    -- e( E(V(s)), E(W(s)) ) / e( E(Y(s)), G ) == e( E(h(s)), E(t(s)) )
    checkD = (e sumV sumW |/| e sumY vE1) |=| e pEh vEt

    uEvio = vEvio <~*> instances -- E(Vio(s))
    sumV = vEv0 |+| uEvio |+| pEvJ -- E(V(s))
    sumW = vEw0 |+| pE'w -- E(W(s))
    sumY = vEy0 |+| pEy -- E(Y(s))
    e = pairing bn254'gt
{-# INLINEABLE zkverify #-}

-- | Examine the prepared zero-knowledge suite
zktest :: Bool -> String -> Wmap Fr -> Wmap Fr -> IO Bool
zktest verbose language witnesses instances = do
  -- Language
  when verbose $ do
    stderr mempty
    stderr language

  -- circuit / Qap
  let circuit = compile'language language
      qap = qap'from'circuit circuit
  when verbose $ do
    stderr mempty
    stderr (pretty circuit)
    stderr mempty
    stderr (pretty qap)

  -- zk-setup
  when verbose $ do
    stderr mempty
    stderr "Creating Evaluation/Verification keys: zk-setup..."
  randos <- toxicwaste
  let (ekey, vkey) = zksetup qap randos

  -- zk-prove
  when verbose $ do
    stderr mempty
    stderr "Generating zk-proof..."
  let out = statement bn254'g1 witnesses circuit
      vec'wit = wire'vals bn254'g1 witnesses circuit
      proof = zkprove qap ekey vec'wit
  when verbose $ info'io 18 ["Prover returns"] [show out]

  -- zk-verify
  let verified = zkverify proof vkey (vec'fromWmap instances)
  when verbose $ do
    stderr mempty
    stderr "Verifying zk-proof..."
    info'io
      18
      ["Statement", "Verified"]
      [show . w'val $ instances ~> "return", show verified]
  pure verified
{-# INLINEABLE zktest #-}

-----------------------

-- | Helpers
decode'file :: forall proxy a. (Store a) => proxy a -> FilePath -> IO a
decode'file _ f =
  do
    bytes <- B.readFile f
    let decoded = decode bytes :: Either PeekException a
    case decoded of
      Right a -> pure a
      Left e ->
        die . unlines $
          [ "Error, failed to decode file: " ++ f,
            "Found invalid bytes at offset " ++ show (peekExBytesFromEnd e)
          ]

read'input :: (Num a) => FilePath -> IO (Wmap a)
read'input f = do
  bytes <- L.readFile f
  let decoded = J.eitherDecode bytes :: Either String (Map String String)
  case decoded of
    Right inputs ->
      pure . wmap'fromList $ second (fromIntegral . int) <$> toList inputs
    Left e ->
      die . unlines $ ["Error, failed to read inputs from: " ++ f, e]

int :: String -> Integer
int str = case readMaybe str of
  Just a -> a
  _ -> int'from'str str

decode'bytes ::
  forall proxy a.
  (Store a) =>
  proxy a ->
  B.ByteString ->
  Either PeekException a
decode'bytes _ bytes = decode bytes

instance Pretty EvaluationKey

instance Pretty VerificationKey

instance Pretty Proof
