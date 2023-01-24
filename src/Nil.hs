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
  , module Nil.Evaluator
  , module Nil.Field
  , module Nil.Graph
  , module Nil.Lexer
  , module Nil.Parser
  , module Nil.Pinocchio
  , module Nil.Poly
  , module Nil.Qap
  , module Nil.Reorg
  , module Nil.Shamir
  , module Nil.Utils
  , module Nil.Ecdsa
  , module Nil
  )
where

import Nil.Circuit
import Nil.Curve
import Nil.Ecdata
import Nil.Ecdsa
import Nil.Evaluator
import Nil.Field
import Nil.Graph
import Nil.Lexer
import Nil.Parser
import Nil.Pinocchio
import Nil.Poly
import Nil.Qap
import Nil.Reorg
import Nil.Shamir
import Nil.Utils

lang =
  unlines
    [ "language (priv a, priv b, priv c, priv d, priv e)"
    , "let o = 10a + b * -8c + d / e"
    , "let p = o + b / c"
    , "let q = (a + 3b + p * d + e)^2"
    , "let r = a * b * c * d * e"
    , "return o * o^2 / r^8 + p * q"
    ]

c = compile'language lang

rc = reorg'circuit c

t =
  table'from'list
    [ ("a", -1111111)
    , ("b", -2222222)
    , ("c", -3333333)
    , ("d", -4444444)
    , ("e", -5555555)
    ]
    :: Table Fr

gc = export'graph "p.pdf" (write'dot dot'header c)

gr = do
  dot <- write'dot dot'header <$> rc
  export'graph "q.pdf" dot

ec = eval'circuit def'curve t c

er = eval'circuit def'curve t <$> rc

retc = ec ! "return"

retr = (! "return") <$> er
