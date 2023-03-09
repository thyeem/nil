{-# LANGUAGE RecordWildCards #-}

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
    [ "language (priv e, priv r, priv s, pub z)"
    , -- , "return e^2 + (e + (r + s))^2 / (z * r * s)"
      "return (e+r)^5"
    ]

c = compile'language lang :: Circuit Fr

-- e = 8464813805670834410435113564993955236359239915934467825032129101731355555480 :: Fr
e = 323874982374982374987239479283749872397429392472893749 :: Fr

-- r = 13405614924655214385005113554925375156635891943694728320775177413191146574283 :: Fr

r = 234728397239847289374892374982374972398749823749872394328472389479823748923794274 :: Fr

s = 13078933289364958062289426192340813952257377699664878821853496586753686181509 :: Fr

z = 4025919241471660438673811488519877818316526842848831811191175453074037299584 :: Fr

w = wmap'fromList [("e", e), ("r", r), ("s", s), ("z", z)] :: Wmap Fr

wmap = extend'wire bn254'g1 <$> w

-- ret = e ^ 2 + (e + r) / (z * r * s)
-- ret = z * s + r * z ^ 5 + (e + r) ^ 2
ret = (e + r) ^ 5

-- ret = e ^ 2 + (e + (r + s)) ^ 2 / (z * r * s)

out = do
  r@Circuit {..} <- reorg'circuit c
  let xr = r {c'gates = extend'gate bn254'g1 <$> c'gates}
  pure $ eval'circuit wmap xr ~> return'key

p = export'graph "orig.pdf" (write'dot dot'header c)

q = do
  dot <- write'dot dot'header <$> reorg'circuit c
  export'graph "reorg.pdf" dot

n = do
  dot <- write'dot dot'header <$> (nilify'circuit <=< reorg'circuit $ c)
  export'graph "nil.pdf" dot

sig = nil'init bn254'g1 bn254'g2 c

omap = omap'from'gates . (c'gates . n'circuit)

t = do
  s <- sig
  signed <- nil'sign wmap s
  let m = eval'circuit wmap (n'circuit signed)

  let _R = unil' . w'val $ m ~> "return"
  let (_P, _C) = n'key signed
  pure $ pairing _R _C == pairing _P _C ^ ret

test = do
  sig@Nilsig {..} <- sig

  let omap = omap'from'gates . c'gates $ n'circuit
      gmap = gmap'from'omap omap
      entries = find'entries omap
      amps = find'amps omap

      delta = 2
      epsilon = 2
      alpha = 2
      beta = 2
  undefined

m = do
  r@Circuit {..} <- reorg'circuit c
  shifted <- concat <$> mapM shift'gate c'gates
  let rc = r {c'gates = shifted}
  let dot = write'dot dot'header rc
  export'graph "shifted.pdf" dot

triplet = do
  s <- sig
  let o = omap s
  let amps = find'amps o
  let p = filter (prin'amp'p o) amps
  let e = filter (entry'amp'p o) amps
  let end = find'end'amp o
  pure (amps, p, e, end)
