{-# LANGUAGE DataKinds #-}

{- |
 Module      : Nil
 License     : MIT
 Maintainer  : Francis Lim <thyeem@gmail.com>
 Stability   : experimental
-}
module Nil
  ( module Nil.Base
  , module Nil.Circuit
  , module Nil.Curve
  , module Nil.Data
  , module Nil.Ecdata
  , module Nil.Ecdsa
  , module Nil.Eval
  , module Nil.Field
  , module Nil.Graph
  , module Nil.Lexer
  , module Nil.Parser
  , module Nil.Pairing
  , module Nil.Pinocchio
  , module Nil.Poly
  , module Nil.Qap
  , module Nil.Reorg
  , module Nil.Shamir
  , module Nil.Sign
  , module Nil.Utils
  , module Nil
  )
where

import Data.Map (elems)
import Nil.Base
import Nil.Circuit
import Nil.Curve
import Nil.Data
import Nil.Ecdata
import Nil.Ecdsa
import Nil.Eval
import Nil.Field
import Nil.Graph
import Nil.Lexer
import Nil.Pairing
import Nil.Parser
import Nil.Pinocchio
import Nil.Poly
import Nil.Qap
import Nil.Reorg
import Nil.Shamir
import Nil.Sign
import Nil.Utils

type NP =
  Primefield
    21888242871839275222246405745257275088696311157297823662689037894645226208583

-- lang =
--   unlines
--     [ "language (priv a, priv b, pub c, priv d, priv e)"
--     , -- "let q = a + 3b + p * d / e"
--       -- [ "language (priv w)"
--       -- , "return w + w"
--       "return e * (((a + a*b)^2) * (c+d))"
--     ]

-- t =
--   table'from'list
--     -- [ ("a", 3)
--     -- , ("b", 3)
--     -- , ("c", 3)
--     -- , ("d", 3)
--     -- , ("e", 3)
--     [("w", 3)]
--     :: W'table NP

-- c = compile'language lang

-- r circuit = export'graph "r.pdf" (write'dot dot'header circuit)

-- p = export'graph "p.pdf" (write'dot dot'header c)

-- q = do
--   dot <- write'dot dot'header <$> reorg'circuit c
--   export'graph "q.pdf" dot

-- initial = init'nilsig bn254'g1 bn254'g2 c

-- otab = otab'from'gates . c'gates . nil'circuit

-- gtab = gtab'from'otab

-- eval sig = do
--   eval'circuit bn254'g1 t (nil'circuit sig)

-- sig = do
--   init <- initial
--   let ot = otab init
--   let gt = gtab ot
--   nilsign bn254'g1 init t

-- ret = (~> "return") . eval

-- pair'pc sig fval =
--   let (phi, chi) = nil'key sig
--    in pairing phi chi ^ fval

-- pair'r sig =
--   let r = p'from'wire bn254'g1 (ret sig)
--    in pairing r g2

lang =
  unlines
    -- [ "language (priv e, priv r, priv s, pub z)"
    -- , "let k = (z + r * e) / s * z"
    -- , "let P = [e]"
    -- , "let R = [k]"
    -- , "let o = if (:R - r) == 0 then :P else :R"
    -- "return k"
    [ "language (priv a, pub b)"
    , "let c = a + a + a + a / b"
    , "return c"
    ]

c = compile'language lang :: Circuit Fr

xc = extend'circuit bn254'g1 c

xw = extend'wire bn254'g1 <$> t

out = statement xw xc

vec'wit = wire'vals xw xc

t =
  wmap'fromList
    [ -- ( "e"
      -- , 8464813805670834410435113564993955236359239915934467825032129101731355555480
      -- )
      -- ,
      -- ( "r"
      -- , 13405614924655214385005113554925375156635891943694728320775177413191146574283
      -- )
      -- ,
      -- ( "s"
      -- , 13078933289364958062289426192340813952257377699664878821853496586753686181509
      -- )
      -- ,
      -- ( "z"
      -- , 4025919241471660438673811488519877818316526842848831811191175453074037299584
      -- )
      ("a", 123)
    , ("b", 345)
    ]
    :: Wmap Fr

inst =
  wmap'fromList
    [ -- ("return", 7806213647036349733094634197439450330907203820135782440392845076885283171317)
      -- ( "return"
      -- , 20546328083791890245710917085664594543309426573230401055874323960053340664311
      -- )

      -- ( "z"
      -- , 4025919241471660438673811488519877818316526842848831811191175453074037299584
      -- )
      ("return", 8945629695447355960396357130670364601406722841909161862207092145817939124665)
      -- , ("b", 345)
    ]
    :: Wmap Fr

zkt = zktest True lang t inst

qap = qap'from'circuit c
