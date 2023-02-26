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
    , "return e^2 + (e + (r + s))^2 / (z * r * s)"
    ]

c = compile'language lang :: Circuit Fr

e = 8464813805670834410435113564993955236359239915934467825032129101731355555480 :: Fr

r = 13405614924655214385005113554925375156635891943694728320775177413191146574283 :: Fr

s = 13078933289364958062289426192340813952257377699664878821853496586753686181509 :: Fr

z = 4025919241471660438673811488519877818316526842848831811191175453074037299584 :: Fr

t = wmap'fromList [("e", e), ("r", r), ("s", s), ("z", z)] :: Wmap Fr

ret = e ^ 2 + (e + r) / (z * r * s)

out = do
  r <- reorg'circuit c
  pure $ eval'circuit bn254'g1 t r ~> return'key

p = export'graph "orig.pdf" (write'dot dot'header c)

q = do
  dot <- write'dot dot'header <$> reorg'circuit c
  export'graph "reorg.pdf" dot

n = do
  dot <- write'dot dot'header <$> (nilify'circuit <=< reorg'circuit $ c)
  export'graph "nil.pdf" dot

sig = init'sig bn254'g1 bn254'g2 c

omap = omap'from'gates . c'gates . nil'circuit

ff = undefined

-- dummy sign test

tt = do
  let w = 1 :: Fr
  a@(aw, ad, ae) <- triple_ 1
  let shift_a = shift_ ad ae
  let net_a = lift_ (w * ad)
  -- pure $ lift_ aw + shift_a == net_a

  b@(bw, bd, be) <- triple_ aw
  let shift_b = (shift_a ~* bd) + shift_ bd be
  let net_b = lift_ (w * ad * bd)

  c@(cw, cd, ce) <- triple_ bw
  let shift_c = (shift_b ~* cd) + shift_ cd ce
  let net_c = lift_ (w * ad * bd * cd)

  -- pure $ lift_ cw + shift_c == net_c

  let secret = 123328478237492374239847123123 :: Fr
  s@(sw, sd, se) <- triple_ secret
  let entry = sw * cw
  let shift_s = shift_c ~* sw + lift_ (-ad * bd * cd * sd * se)
  let net_s = lift_ (secret * ad * bd * cd * sd)
  pure $ lift_ entry + shift_s == net_s

shift_ delta epsilon = c'g bn254'g1 ~* (-delta * epsilon)

lift_ = (c'g bn254'g1 ~*)

triple_ w = do
  d <- ranf :: IO Fr
  e <- ranf :: IO Fr
  pure (d * (w + e), d, e)
