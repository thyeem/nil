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

import Control.Monad ((<=<))
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
    [ "language (priv e, priv r, priv s, pub z)",
      "return e^3 * 7e + (5r - 3s) ^4 + (e/r-s)^13 / 3z * 2r * s"
    ]

c = compile'language lang :: Circuit Fr

e = 8464813805670834410435113564993955236359239915934467825032129101731355555480 :: Fr

r = 13405614924655214385005113554925375156635891943694728320775177413191146574283 :: Fr

s = 13078933289364958062289426192340813952257377699664878821853496586753686181509 :: Fr

z = 4025919241471660438673811488519877818316526842848831811191175453074037299584 :: Fr

w = wmap'fromList [("e", e), ("r", r), ("s", s), ("z", z)] :: Wmap Fr

wmap = extend'wire bn254'g1 <$> w

ret = statement bn254'g1 w c

out = do
  r@Circuit {..} <- reorg'circuit c
  let xr = r {c'gates = extend'gate bn254'g1 <$> c'gates}
  pure . w'val $ eval'circuit wmap xr ~> return'key

omap = omap'from'gates . (c'gates . n'circuit)

sig = nil'init bn254'g1 bn254'g2 c

p = g'circuit c "orig.pdf"

q = g'reorged c "reorg.pdf"

n = do
  s <- sig
  g'sig s "nil.pdf"

m sig' = do
  g'sig sig' "signed.pdf"

t = do
  s <- sig
  ss <- nil'sign wmap1 s
  sss <- nil'sign wmap2 ss
  let m = eval'circuit wmap (n'circuit sss)
  let _R = unil' . w'val $ m ~> "return"
  let (_P, _C) = n'key sss
  pure $ pairing bn254'gt _R _C == pairing bn254'gt _P _C ^ ret

wmap1 = extend'wire bn254'g1 <$> wmap'fromList [("e", e), ("r", r)]

wmap2 = extend'wire bn254'g1 <$> wmap'fromList [("s", s), ("z", z)]
