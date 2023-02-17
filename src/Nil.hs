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

lang =
  unlines
    -- [ "language (priv a, priv b, pub c, priv d, priv e)"
    -- , "return a+b"
    -- , "let o = 10a + b * c * d / e"
    -- , "let p = o^3 + b / c"
    -- , "let q = a + 3b + p * d / e"
    -- , "let r = a * b / c * d / e"
    -- , "return o * o^2 / r^3 + p * q"
    [ "language (priv w)"
    , "return w + w"
    -- , "return a^3 + a*b + (a * 7b) + 5*3"
    ]

t =
  table'from'list
    -- [ ("a", 3)
    -- , ("b", 3)
    -- , ("c", 3)
    -- , ("d", 3)
    -- , ("e", 3)
    [("w", 3)]
    :: W'table NP

c = compile'language lang

r circuit = export'graph "r.pdf" (write'dot dot'header circuit)

p = export'graph "p.pdf" (write'dot dot'header c)

q = do
  dot <- write'dot dot'header <$> reorg'circuit c
  export'graph "q.pdf" dot

initial = init'nilsig bn128G1 bn128G2 c

otab = otab'from'gates . c'gates . nil'circuit

gtab = gtab'from'otab

eval sig = do
  eval'circuit bn128G1 t (nil'circuit sig)

sig = do
  init <- initial
  let ot = otab init
  let gt = gtab ot
  nilsign bn128G1 bn128G2 init t

ret = (~> "return") . eval

pair'pc sig fval =
  let (phi, chi) = nil'key sig
   in pairing phi chi ^ fval

pair'r sig =
  let r = p'from'wire bn128G1 (ret sig)
   in pairing r gG2
