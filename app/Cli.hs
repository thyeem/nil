{-# LANGUAGE TemplateHaskell #-}

module Cli where

import Data.Version (showVersion)
import Development.GitRev (gitBranch, gitHash)
import Options.Applicative
import Paths_nil (version)

data Opts = Opts
  { o'quite :: Bool
  , o'command :: Command
  }

data Command
  = Setup Bool String
  | Prove
  | Verify
  | Sign
  | Check
  | View String
  | Test Bool String String String
  deriving (Show)

type Command' = Mod CommandFields Command

opts'parser :: ParserInfo Opts
opts'parser = info (helper <*> ver <*> global'opts) mempty
 where
  ver =
    (infoOption ver'str . mconcat)
      [long "version", short 'V', help "Print version of the program"]
  ver'str =
    unwords
      ["nil", showVersion version, "(" ++ $(gitBranch) ++ ")", $(gitHash)]
  global'opts =
    Opts
      <$> (switch . mconcat)
        [ long "quiet"
        , short 'q'
        , help "Decrease verbosity"
        ]
      <*> (hsubparser . mconcat)
        [setup, prove, verify, sign, check, view, test]

setup :: Command'
setup =
  command
    "setup"
    $ info options (progDesc "(zkp) zk-SNARKs setup proceeds")
 where
  options =
    Setup
      <$> (switch . mconcat)
        [ long "graph"
        , short 'g'
        , help "Export a circuit as graph"
        ]
      <*> (strArgument . mconcat)
        [ metavar "LANGUAGE"
        , help "Language file"
        ]

prove :: Command'
prove =
  command
    "prove"
    (info (pure Prove) (progDesc "(zkp) Generate zk-proofs"))

verify :: Command'
verify =
  command
    "verify"
    (info (pure Verify) (progDesc "(zkp) Verify zk-proofs"))

sign :: Command'
sign =
  command
    "sign"
    (info (pure Sign) (progDesc "(mpc) Partially evaluate circuit with secrets"))

check :: Command'
check =
  command
    "check"
    (info (pure Check) (progDesc "(mpc) Fully evaluate circuit and check validity"))

view :: Command'
view =
  command
    "view"
    (info options (progDesc "Print files in a human-readable format"))
 where
  options =
    View
      <$> (strArgument . mconcat)
        [ metavar "FILE"
        , help "Any types of files involved in this program"
        ]

test :: Command'
test =
  command
    "test"
    $ info options (progDesc "Examine prepared test suites using inputs")
 where
  options =
    Test
      <$> (switch . mconcat)
        [ long "demo"
        , help "Run a sample demo"
        ]
      <*> (strOption . mconcat)
        [ long "lang"
        , short 'l'
        , metavar "FILE"
        , help "Language file"
        ]
      <*> (strOption . mconcat)
        [ long "wit"
        , short 'w'
        , metavar "FILE"
        , help "Witness file in JSON"
        ]
      <*> (strOption . mconcat)
        [ long "inst"
        , short 'i'
        , metavar "FILE"
        , help "Instance file"
        ]
