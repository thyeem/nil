{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Cli (Command (..), Opts (..), opts'parser)
import Control.Monad (unless, when)
import Control.Monad.Extra (unlessM)
import qualified Data.ByteString as B
import Data.Either (fromRight, isRight)
import Data.List (intercalate)
import Data.Proxy
import Data.Store (PeekException, decode, encode)
import Nil
import Options.Applicative (execParser)
import System.Directory (doesFileExist)
import System.FilePath.Posix (takeDirectory)

-- | Entry point of this program
main :: IO ()
main = execParser opts'parser >>= project

-- | main program
project :: Opts -> IO ()
project opts@Opts {..} = do
  case o'command of
    Setup {} -> setup opts
    Prove {} -> prove opts
    Verify {} -> verify opts
    Init {} -> init' opts
    Sign {} -> print "sign"
    Check {} -> print "check"
    View {} -> view opts
    Test {} -> print "test"
    Demo {} -> demo opts

setup :: Opts -> IO ()
setup Opts {..} = do
  let Setup graph language = o'command
  unlessM
    (doesFileExist language)
    (err $ "Error, language file does not exist: " ++ language)
  crs <- toxicwaste
  circuit <- compile'language <$> readFile language
  let qap = qap'from'circuit circuit
      (ekey, vkey) = zksetup qap crs
      circ'id = hex'from'bytes . sha256 . encode $ circuit
      path = takeDirectory language
      file'circ = circ'id ++ ".circ"
      file'ekey = circ'id ++ ".ekey"
      file'vkey = circ'id ++ ".vkey"
  B.writeFile (path ++ "/" ++ file'circ) . encode $ circuit
  B.writeFile (path ++ "/" ++ file'ekey) . encode $ ekey
  B.writeFile (path ++ "/" ++ file'vkey) . encode $ vkey

  -- setup result (3 files: circuit, evaluation key, verification key),
  -- and their SHA-256 hashes as fingerprints
  unless o'quite $ do
    info'io
      ["filepath", "Circuit", "(hash)", "E-key", "(hash)", "V-key", "(hash)"]
      [ path,
        file'circ,
        circ'id,
        file'ekey,
        hex'from'bytes . sha256 . encode $ ekey,
        file'vkey,
        hex'from'bytes . sha256 . encode $ vkey
      ]
  -- export graph
  when graph $ do
    let file'dag = circ'id ++ ".pdf"
    export'graph file'dag (write'dot dot'header circuit)
    unless o'quite (info'io ["Graph"] [file'dag])

prove :: Opts -> IO ()
prove Opts {..} = do
  let Prove circuit ekey wit = o'command
  circuit_ <- decode'file (Proxy :: Proxy (Circuit Fr)) circuit
  ekey_ <- decode'file (Proxy :: Proxy EvaluationKey) ekey
  witness_ <- read'input wit :: IO (Wmap Fr)
  let qap = qap'from'circuit circuit_
      out = statement bn254'g1 witness_ circuit_
      vec'wit = wire'vals bn254'g1 witness_ circuit_
      proof = zkprove qap ekey_ vec'wit
      path = takeDirectory wit
      pfID = hex'from'bytes . sha256 . encode $ proof
      file'proof = pfID ++ ".pf"
  B.writeFile (path ++ "/" ++ file'proof) . encode $ proof
  unless o'quite $ do
    info'io
      ["Eval (out)", "filepath", "Proof" :: String]
      [show (toInteger out), path, file'proof]

verify :: Opts -> IO ()
verify Opts {..} = do
  let Verify proof vkey inst = o'command
  proof_ <- decode'file (Proxy :: Proxy Proof) proof
  vkey_ <- decode'file (Proxy :: Proxy VerificationKey) vkey
  instance_ <- read'input inst :: IO (Wmap Fr)
  let claim = w'val $ instance_ ~> "return"
      verified = zkverify proof_ vkey_ (vec'fromWmap instance_)
  unless o'quite $ do
    info'io
      ["Statement", "Verified" :: String]
      [show (toInteger claim), show verified]

init' :: Opts -> IO ()
init' Opts {..} = do
  let Init graph language = o'command
  unlessM
    (doesFileExist language)
    (err $ "Error, language file does not exist: " ++ language)
  circuit <- compile'language <$> readFile language
  sig@Nilsig {..} <-
    nil'init bn254'g1 bn254'g2 bn254'gt circuit ::
      IO (Nilsig BN254 BN254'G2 Fr G1)
  let path = takeDirectory language
      hash = hex'from'bytes $ hash'sig bn254'gt sig
      file'sig = hash ++ ".sig"
  B.writeFile (path ++ "/" ++ file'sig) . encode $ sig

  unless o'quite $ do
    info'io
      ["filepath", "Nil-sig", "(hash)"]
      [path, hash ++ ".sig", hash]

  -- export graph
  when graph $ do
    let file'dag = hash ++ ".pdf"
    export'graph file'dag (write'dot dot'header circuit)
    unless o'quite (info'io ["graph"] [file'dag])

view :: Opts -> IO ()
view Opts {..} =
  do
    let View graph reorg file = o'command
    unlessM
      (doesFileExist file)
      (err $ "Error, file file does not exist: " ++ file)
    bytes <- B.readFile file
    let circuit = decode'bytes (Proxy :: Proxy (Circuit Fr)) bytes
        ekey = decode'bytes (Proxy :: Proxy EvaluationKey) bytes
        vkey = decode'bytes (Proxy :: Proxy VerificationKey) bytes
        proof = decode'bytes (Proxy :: Proxy Proof) bytes
        nilsig = decode'bytes (Proxy :: Proxy (Nilsig BN254 BN254'G2 Fr G1)) bytes
        unwrap = fromRight (die mempty)
    if
        | isRight circuit -> do
            circ <-
              if reorg
                then reorg'circuit (unwrap circuit)
                else pure (unwrap circuit)
            let circ'id = hex'from'bytes . sha256 . encode $ circ
            if graph
              then do
                let file = takeDirectory file ++ "/" ++ circ'id ++ ".pdf"
                export'graph file (write'dot dot'header circ)
                unless o'quite (ok file)
              else do pp . unwrap $ circuit
        | isRight ekey -> pp . unwrap $ ekey
        | isRight vkey -> pp . unwrap $ vkey
        | isRight proof -> pp . unwrap $ proof
        | isRight nilsig -> pp . unwrap $ nilsig
        | otherwise -> pp . str'from'bytes $ bytes

test :: IO ()
test = undefined

demo :: Opts -> IO ()
demo Opts {..} = do
  let Demo list item = o'command
  when list $ do
    info'io
      ["mpc", "zkp"]
      [ "multi-party computation demo using nil-sign",
        "zero-knowledge proof demo using pinocchio protocol"
      ]
    err mempty
  when (item == "mpc") $ demo'mpc (not o'quite)
  when (item == "zkp") $ demo'zkp (not o'quite)

demo'zkp :: Bool -> IO ()
demo'zkp verbose =
  zktest
    verbose
    ( intercalate
        "\n\t"
        [ "language (priv e, priv r, priv s, pub z)",
          "let k = (z + r * e) / s",
          "let P = [e]",
          "let R = [k]",
          "let o = if (:R - r) == 0 then :P else :R",
          "return o"
        ]
    )
    ( wmap'fromList
        [ ("e", 8464813805670834410435113564993955236359239915934467825032129101731355555480),
          ("r", 13405614924655214385005113554925375156635891943694728320775177413191146574283),
          ("s", 13078933289364958062289426192340813952257377699664878821853496586753686181509),
          ("z", 4025919241471660438673811488519877818316526842848831811191175453074037299584)
        ] ::
        Wmap Fr
    )
    ( wmap'fromList
        [ ("return", 20546328083791890245710917085664594543309426573230401055874323960053340664311),
          ("z", 4025919241471660438673811488519877818316526842848831811191175453074037299584)
        ]
    )
    >>= print

demo'mpc :: Bool -> IO ()
demo'mpc verbose =
  nil'test
    verbose
    ( intercalate
        "\n\t"
        [ "language (priv e, priv r, priv s, pub z)",
          "return ((e+r*s)^4 + s*z)^3 / z*r*s"
        ]
    )
    ( wmap'fromList
        [ ("e", 8464813805670834410435113564993955236359239915934467825032129101731355555480),
          ("r", 13405614924655214385005113554925375156635891943694728320775177413191146574283),
          ("s", 13078933289364958062289426192340813952257377699664878821853496586753686181509),
          ("z", 4025919241471660438673811488519877818316526842848831811191175453074037299584),
          ("return", 9736209953418122309806155361367034953823483591771807982224153372278884065086)
        ] ::
        Wmap Fr
    )
    >>= print
