{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Cli
import Nil (ok)
import Options.Applicative (execParser)

-- | Entry point of this program
main :: IO ()
main = execParser opts'parser >>= nil

-- | main program
nil :: Opts -> IO ()
nil opts@Opts {..} = do
  case o'command of
    Setup {} -> ok "setup"
    Prove {} -> ok "prove"
    Verify {} -> ok "verify"
    Sign {} -> ok "sign"
    Check {} -> ok "check"
    View {} -> ok "view"
    Test {} -> ok "test"
