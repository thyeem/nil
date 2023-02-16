{- |
 Module      : Nil
 License     : MIT
 Maintainer  : Francis Lim <thyeem@gmail.com>
 Stability   : experimental
-}
module Nil
  ( module Nil.Circuit
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

lang =
  unlines
    -- [ "language (priv a, priv b, pub c, priv d, priv e)"
    -- , "let o = 10a + b * c * d / e"
    -- , "let p = o^3 + b / c"
    -- , "let q = a + 3b + p * d / e"
    -- , "let r = a * b / c * d / e"
    -- , "return o * o^2 / r^3 + p * q"
    [ "language (pub a, priv b, priv c)"
    , "return a^2 + 2*b + a*c"
    -- , "return a^3 + a*b + a + 7b + 5 * 3"
    -- , "return a + (5*7) + 10"
    -- [ "language (priv w)"
    -- , "return w^3 + w + 5"
    ]

c = compile'language lang

t =
  table'from'list
    [ ("a", -1111111)
    , ("b", -2222222)
    , ("c", -3333333)
    , ("d", -4444444)
    , ("e", -5555555)
    , ("w", 3)
    ]
    :: W'table Fr

g circuit = export'graph "p.pdf" (write'dot dot'header circuit)

g' = do
  dot <- write'dot dot'header <$> reorg'circuit c
  export'graph "q.pdf" dot

e = eval'circuit def'curve t c

e' = eval'circuit def'curve t <$> reorg'circuit c

o = w'val . (~> "return")

sig = init'sig <$> reorg'circuit c

---------

otab = otab'from'gates . c'gates <$> reorg'circuit c

gtab = gtab'from'otab <$> otab

t'amp key = do
  ot <- otab
  let gt = gtab'from'otab ot
      g = filter (\(gate, _) -> (w'key . g'lwire $ gate) == key) (elems ot)
      amp = filter (\(gate, _) -> xor' amp'wirep gate) (elems ot)
  pp amp
  pure $ get'amp gt (fst . head $ g)

t'shift i = do
  ot <- otab
  let gt = gtab'from'otab ot
      g = filter (\(gate, _) -> g'op gate /= End && xor' entry'wirep gate) (elems ot)
  pp g
  pure $ get'shift ot gt (fst $ g !! i)

t'sign = do
  sig <- init'sig c
  let ot = otab'from'gates . c'gates . n'sig $ sig
  let gt = gtab'from'otab ot
  nilsign bn128G1 sig t
