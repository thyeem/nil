{-# LANGUAGE RecordWildCards #-}

module Nil.Graph
  ( write'dot
  , export'graph
  , dot'header
  , g'sig
  , g'circuit
  , g'reorged
  )
where

import Control.Monad (when)
import Nil.Circuit
import Nil.Reorg (amp'wirep, frozen'wirep, reorg'circuit, shift'wirep)
import Nil.Sign (Nilsig (..))
import Nil.Utils (die)
import System.Exit (ExitCode (ExitSuccess))
import System.Process (readProcessWithExitCode)

-- | Export a given dot script to a graph file as pdf
export'graph :: FilePath -> String -> IO ()
export'graph file script = do
  (e, _, err) <-
    readProcessWithExitCode
      "dot"
      ["-Tpdf", "-o" ++ file]
      script
  when
    (e /= ExitSuccess)
    (die $ "Failed to convert - " ++ err)

-- | Convert a circuit into a dot-language script
write'dot :: Eq f => String -> Circuit f -> String
write'dot header circuit =
  unwords
    ["digraph G {", header, write'gates circuit, "}"]

dot'header :: String
dot'header = "size=\"32,32\"; rankdir=LR;"

write'gates :: Eq f => Circuit f -> String
write'gates Circuit {..} =
  unwords $ write'gate c'pubs c'privs <$> c'gates

write'gate :: Eq f => [String] -> [String] -> Gate f -> String
write'gate instances witnesses Gate {..}
  | key g'lwire == "return" =
      unwords [edge g'rwire g'lwire, style g'lwire]
  | otherwise =
      unwords
        [ edge g'lwire g'owire
        , style g'lwire
        , edge g'rwire g'owire
        , style g'rwire
        , key g'owire
        , "["
        , "shape=doublecircle,"
        , "style=filled,"
        , "fontsize=18,"
        , "fillcolor=" ++ color ++ ","
        , "label=\"" ++ show g'op ++ "\"];"
        ]
 where
  key wire
    | out'wirep wire = tail (w'key wire)
    | (const'wirep wire || shift'wirep wire) && wire == g'lwire =
        "_" ++ key g'owire ++ "L"
    | (const'wirep wire || shift'wirep wire) && wire == g'rwire =
        "_" ++ key g'owire ++ "R"
    | otherwise = w'key wire

  edge from to =
    unwords
      [ key from
      , "->"
      , key to
      , "[color=" ++ edge'color from ++ "];"
      ]

  edge'color wire
    | w'recip wire = "red"
    | out'wirep wire = "blue"
    | otherwise = "black"

  color
    | g'op == Add = "ivory"
    | g'op == Mul = "lavender"
    | otherwise = "white"

  style wire
    | frozen'wirep wire =
        unwords
          [ key wire
          , "[shape=egg,style=filled,fillcolor=gray,fontsize=20,label=\"?\"];"
          ]
    | shift'wirep wire =
        unwords
          [ key wire
          , "[shape=egg,style=filled,fillcolor=none,fontsize=18,"
              ++ "label=<-&delta;<sub>i</sub>&epsilon;<sub>i</sub>>];"
          ]
    | amp'wirep wire =
        unwords
          [ key wire
          , "[shape=egg,style=filled,fillcolor=lightcyan,fontsize=18,"
              ++ "label=<&beta;<sub>ij</sub>/&delta;<sub>ij</sub>>];"
          ]
    | const'wirep wire =
        unwords
          [ key wire
          , "[shape=egg,style=dashed,label=Const,fontsize=18];"
          ]
    | w'key wire `elem` instances =
        unwords
          [ key wire
          , "[shape=egg,style=filled,fillcolor=lightgreen,fontsize=30];"
          ]
    | w'key wire `elem` witnesses =
        unwords
          [ key wire
          , "[shape=egg,style=filled,fillcolor=pink,fontsize=30];"
          ]
    | otherwise =
        mempty

------------------------
-- Debugging tool (tmp)
------------------------
g'circuit :: Eq a => Circuit a -> String -> IO ()
g'circuit circuit f = export'graph f (write'dot dot'header circuit)

g'reorged :: (Eq a, Num a) => Circuit a -> String -> IO ()
g'reorged circuit f = do
  dot <- write'dot dot'header <$> reorg'circuit circuit
  export'graph f dot

g'sig :: (Eq q, Eq r) => Nilsig i r q p -> String -> IO ()
g'sig sig f = do
  let dot = write'dot dot'header (n'circuit sig)
  export'graph f dot
