{-# LANGUAGE TemplateHaskell #-}

module Cli where

import Data.Version (showVersion)
import Development.GitRev (gitBranch, gitHash)
import Options.Applicative
import Paths_nil (version)

data Opts = Opts
  { o'quite :: Bool,
    o'command :: Command
  }

data Command
  = Setup Bool String
  | Prove String String String
  | Verify String String String
  | Init Bool String
  | Sign String String
  | Check String String
  | View Bool Bool String
  | Test String String String
  | Demo Bool String
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
          [ long "quiet",
            short 'q',
            help "Decrease verbosity"
          ]
        <*> (hsubparser . mconcat)
          [ setup,
            prove,
            verify,
            init',
            sign,
            check,
            view,
            test,
            demo,
            metavar "Command"
          ]

setup :: Command'
setup =
  command
    "setup"
    $ info options (progDesc "(zkp) zk-SNARKs setup proceeds")
  where
    options =
      Setup
        <$> (switch . mconcat)
          [ long "graph",
            short 'g',
            help "Export a circuit as graph"
          ]
        <*> (strArgument . mconcat)
          [ metavar "FILE",
            help "Language file"
          ]

prove :: Command'
prove =
  command
    "prove"
    (info options (progDesc "(zkp) Generate zk-proofs"))
  where
    options =
      Prove
        <$> (strOption . mconcat)
          [ long "circ",
            short 'c',
            metavar "FILE",
            help "Circuit file"
          ]
        <*> (strOption . mconcat)
          [ long "key",
            short 'k',
            metavar "FILE",
            help "Evaluation key file"
          ]
        <*> (strArgument . mconcat)
          [ metavar "FILE",
            help "Witness file in JSON"
          ]

verify :: Command'
verify =
  command
    "verify"
    (info options (progDesc "(zkp) Verify zk-proofs"))
  where
    options =
      Verify
        <$> (strOption . mconcat)
          [ long "proof",
            short 'p',
            metavar "FILE",
            help "Proof file"
          ]
        <*> (strOption . mconcat)
          [ long "key",
            short 'k',
            metavar "FILE",
            help "Verification key file"
          ]
        <*> (strArgument . mconcat)
          [ metavar "FILE",
            help "Instance file in JSON"
          ]

init' :: Command'
init' =
  command
    "init"
    (info options (progDesc "(mpc) Initialize nil-signature"))
  where
    options =
      Init
        <$> (switch . mconcat)
          [ long "graph",
            short 'g',
            help "Export a circuit as graph"
          ]
        <*> (strArgument . mconcat)
          [ metavar "FILE",
            help "Language file"
          ]

sign :: Command'
sign =
  command
    "sign"
    (info options (progDesc "(mpc) Sign nil-signature with given secrets"))
  where
    options =
      Sign
        <$> (strOption . mconcat)
          [ long "secrets",
            short 's',
            metavar "FILE",
            help "Secret file"
          ]
        <*> (strOption . mconcat)
          [ long "key",
            short 'k',
            metavar "FILE",
            help "key file"
          ]

check :: Command'
check =
  command
    "check"
    (info options (progDesc "(mpc) Evaluate nil-signature to check validity"))
  where
    options =
      Check
        <$> (strOption . mconcat)
          [ long "",
            short 's',
            metavar "FILE",
            help "Proof file"
          ]
        <*> (strOption . mconcat)
          [ long "key",
            short 'k',
            metavar "FILE",
            help "key file"
          ]

view :: Command'
view =
  command
    "view"
    (info options (progDesc "Print files in a human-readable format"))
  where
    options =
      View
        <$> (switch . mconcat)
          [ long "graph",
            short 'g',
            help "(circuit-only) Export a circuit as graph"
          ]
        <*> (switch . mconcat)
          [ long "reorg",
            short 'r',
            help "(circuit-only) Reorg a circuit"
          ]
        <*> (strArgument . mconcat)
          [ metavar "FILE",
            help "Any types of files involved in this program"
          ]

test :: Command'
test =
  command
    "test"
    $ info options (progDesc "Examine prepared test suites using inputs")
  where
    options =
      Test
        <$> (strOption . mconcat)
          [ long "lang",
            short 'l',
            metavar "FILE",
            help "Language file"
          ]
        <*> (strOption . mconcat)
          [ long "wit",
            short 'w',
            metavar "FILE",
            help "Witness file in JSON"
          ]
        <*> (strOption . mconcat)
          [ long "inst",
            short 'x',
            metavar "FILE",
            help "Instance file in JSON"
          ]

demo :: Command'
demo =
  command
    "demo"
    $ info options (progDesc "Run sample demos prepared")
  where
    options =
      Demo
        <$> (switch . mconcat)
          [ long "list",
            short 'l',
            help "List demos available"
          ]
        <*> (strArgument . mconcat)
          [ metavar "ITEM",
            help "Choose one from the available demos",
            value "zkp",
            showDefault
          ]
