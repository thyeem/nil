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
  | Sign Bool String String
  | Check String String String
  | View Bool Bool Bool Bool Bool String
  | Test Bool String String String
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
          [ metavar "WITNESS",
            help "JSON file of witnesses"
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
          [ metavar "INSTANCE",
            help "JSON file of instances"
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
        <$> (switch . mconcat)
          [ long "graph",
            short 'g',
            help "Export a circuit as graph"
          ]
        <*> (strOption . mconcat)
          [ long "sig",
            short 's',
            metavar "FILE",
            help "Signature file to multi-sign"
          ]
        <*> (strArgument . mconcat)
          [ metavar "SECRETS",
            help "JSON file of secrets"
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
          [ long "hash",
            metavar "HEX",
            value mempty,
            help
              "Check if the signature matches the given hex-string"
          ]
        <*> (strOption . mconcat)
          [ long "sig",
            short 's',
            metavar "FILE",
            help "Signature file to verify"
          ]
        <*> (strArgument . mconcat)
          [ metavar "RETURN",
            help "JSON file of expected f-value"
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
          [ long "hash",
            help "(sig) Disaply hash-value of signature only"
          ]
        <*> (switch . mconcat)
          [ long "nilkey",
            short 'k',
            help "(sig) Disaply nil-key of signature only"
          ]
        <*> (switch . mconcat)
          [ long "graph",
            short 'g',
            help "(circuit/sig) Export a circuit as graph"
          ]
        <*> (switch . mconcat)
          [ long "priv",
            short 'w',
            help "(circuit/sig) Display private secret items only"
          ]
        <*> (switch . mconcat)
          [ long "pub",
            short 'x',
            help "(circuit/sig) Display public info items only"
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
        <$> (switch . mconcat)
          [ long "eval-only",
            short 'e',
            help "Display circuit evaluation result only"
          ]
        <*> (strOption . mconcat)
          [ long "lang",
            short 'l',
            metavar "FILE",
            help "Language file"
          ]
        <*> (strOption . mconcat)
          [ long "data",
            short 'd',
            metavar "FILE",
            help "JSON file of all input entries"
          ]
        <*> (strOption . mconcat)
          [ long "mode",
            short 'm',
            metavar "MODE",
            help "Choose mode to test",
            value "mpc",
            showDefault
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
        <*> (strOption . mconcat)
          [ long "mode",
            short 'm',
            metavar "MODE",
            help "Choose an item from the available demos",
            value "mpc",
            showDefault
          ]
