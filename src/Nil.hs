{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Nil
-- License     : MIT
-- Maintainer  : Francis Lim <thyeem@gmail.com>
-- Stability   : experimental
module Nil
  ( module Nil.Base,
    module Nil.Circuit,
    module Nil.Curve,
    module Nil.Data,
    module Nil.Ecdata,
    module Nil.Ecdsa,
    module Nil.Eval,
    module Nil.Field,
    module Nil.Graph,
    module Nil.Lexer,
    module Nil.Parser,
    module Nil.Pairing,
    module Nil.Pinocchio,
    module Nil.Poly,
    module Nil.Qap,
    module Nil.Reorg,
    module Nil.Shamir,
    module Nil.Sign,
    module Nil.Utils,
    module Nil,
  )
where

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

lang =
  unlines
    [ "language (priv a, pub b, priv c)",
      "return a * b + c"
    ]

c = compile'language lang :: Circuit Fr

rc = reorg'circuit c

sig = nil'init bn254'g1 bn254'g2 bn254'gt c

wmap = wmap'fromList [("a", 10), ("b", 20), ("c", 30), ("return", 230)] :: Wmap Fr

ret = w'val $ wmap ~> return'key

fval = statement bn254'g1 wmap c

rfval = statement bn254'g1 wmap <$> rc

go =
  do
    s <- sig
    signed <- nil'sign bn254'gt (extend'wire bn254'g1 <$> wmap) s
    -- pure verified
    let omap = omap'from'gates . c'gates $ n'circuit signed
        (phi, chi) = n'key signed
        wmap' = extend'wire (p'curve phi) <$> wmap'fromList [(return'key, fval)]
        out = unil' . w'val $ eval'circuit wmap' (n'circuit signed) ~> return'key

    let lp = pairing bn254'gt out chi
    let rp = pairing bn254'gt phi chi ^ fval

    pp lp
    pp rp

    pure $ uncurry (pairing bn254'gt) (n'key s) == uncurry (pairing bn254'gt) (n'key signed)
