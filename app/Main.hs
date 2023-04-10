{-# LANGUAGE RecordWildCards #-}

module Main where

import Cli (Command (..), Opts (..), opts'parser)
import Control.Monad (unless, when)
import Control.Monad.Extra (unlessM)
import qualified Data.ByteString as B
import Data.Either (fromRight, isRight)
import Data.List (intercalate, sort)
import Data.Map (assocs)
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
    Sign {} -> sign opts
    Check {} -> check opts
    View {} -> view opts
    Test {} -> undefined
    Demo {} -> demo opts

setup :: Opts -> IO ()
setup Opts {..} = do
  let Setup graph language = o'command
  guard'file language
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
      12
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
    export'graph (path ++ "/" ++ file'dag) (write'dot dot'header circuit)
    unless o'quite (info'io 12 ["Graph"] [file'dag])

prove :: Opts -> IO ()
prove Opts {..} = do
  let Prove circuit ekey wit = o'command
  guard'file circuit
  guard'file ekey
  guard'file wit
  circuit_ <- decode'file (Proxy :: Proxy (Circuit Fr)) circuit
  ekey_ <- decode'file (Proxy :: Proxy EvaluationKey) ekey
  witness_ <- read'input wit :: IO (Wmap Fr)
  let qap = qap'from'circuit circuit_
      claim = statement bn254'g1 witness_ circuit_
      vec'wit = wire'vals bn254'g1 witness_ circuit_
      proof = zkprove qap ekey_ vec'wit
      path = takeDirectory wit
      pfID = hex'from'bytes . sha256 . encode $ proof
      file'proof = pfID ++ ".pf"
  B.writeFile (path ++ "/" ++ file'proof) . encode $ proof
  unless o'quite $
    info'io
      12
      ["Statement", "filepath", "Proof"]
      [show claim, path, file'proof]
  ok (path ++ "/" ++ file'proof)

verify :: Opts -> IO ()
verify Opts {..} = do
  let Verify proof vkey inst = o'command
  proof_ <- decode'file (Proxy :: Proxy Proof) proof
  vkey_ <- decode'file (Proxy :: Proxy VerificationKey) vkey
  instance_ <- read'input inst :: IO (Wmap Fr)
  let target = w'val $ instance_ ~> return'key
      verified = zkverify proof_ vkey_ (vec'fromWmap instance_)
  unless o'quite $
    info'io
      12
      ["Statement", "Verified"]
      [show target, show verified]
  ok (show verified)

init' :: Opts -> IO ()
init' Opts {..} = do
  let Init graph language = o'command
  guard'file language
  circuit <- compile'language <$> readFile language
  sig <-
    nil'init bn254'g1 bn254'g2 bn254'gt circuit ::
      IO (Nilsig BN254 BN254'G2 Fr G1)
  let path = takeDirectory language
      sig'id = hex'from'bytes . sha256 . encode $ sig
      file'sig = sig'id ++ ".sig"
  B.writeFile (path ++ "/" ++ file'sig) . encode $ sig
  unless o'quite $
    info'io
      12
      ["filepath", "Signature", "(hash)"]
      [path, file'sig, sig'id]
  -- export graph
  when graph $ do
    let file'dag = sig'id ++ ".pdf"
    export'graph
      (path ++ "/" ++ file'dag)
      (write'dot dot'header $ n'circuit sig)
    unless o'quite (info'io 12 ["graph"] [file'dag])

sign :: Opts -> IO ()
sign Opts {..} = do
  let Sign graph sig secrets = o'command
  guard'file sig
  guard'file secrets
  sig_ <- decode'file (Proxy :: Proxy (Nilsig BN254 BN254'G2 Fr G1)) sig
  secrets_ <- read'input secrets :: IO (Wmap Fr)
  signed <- nil'sign bn254'gt (extend'wire bn254'g1 <$> secrets_) sig_
  let path = takeDirectory secrets
      sig'id = hex'from'bytes . sha256 . encode $ signed
      file'sig = sig'id ++ ".sig"
  B.writeFile (path ++ "/" ++ file'sig) . encode $ signed
  unless o'quite $
    info'io
      12
      ["filepath", "Signature", "(hash)"]
      [path, file'sig, sig'id]
  -- export graph
  when graph $ do
    let file'dag = sig'id ++ ".pdf"
    export'graph
      (path ++ "/" ++ file'dag)
      (write'dot dot'header $ n'circuit signed)
    unless o'quite (info'io 12 ["graph"] [file'dag])
  ok (path ++ "/" ++ file'sig)

check :: Opts -> IO ()
check Opts {..} = do
  let Check hash sig ret = o'command
  guard'file sig
  sig_ <- decode'file (Proxy :: Proxy (Nilsig BN254 BN254'G2 Fr G1)) sig
  ret_ <- read'input ret :: IO (Wmap Fr)
  let fval = w'val $ ret_ ~> return'key
      out = unil' . w'val $ eval'circuit mempty (n'circuit sig_) ~> return'key
      verified = nil'check bn254'gt (w'val $ ret_ ~> return'key) sig_
  unless o'quite $
    info'io
      12
      ["Evaluated", "Claimed", "Verified"]
      ["\n" ++ pretty out, show fval, show verified]
  ok (show verified)

view :: Opts -> IO ()
view opts@Opts {..} =
  do
    let View hash nilkey graph priv pub file = o'command
    guard'file file
    bytes <- B.readFile file
    let circuit = decode'bytes (Proxy :: Proxy (Circuit Fr)) bytes
        ekey = decode'bytes (Proxy :: Proxy EvaluationKey) bytes
        vkey = decode'bytes (Proxy :: Proxy VerificationKey) bytes
        proof = decode'bytes (Proxy :: Proxy Proof) bytes
        nilsig = decode'bytes (Proxy :: Proxy (Nilsig BN254 BN254'G2 Fr G1)) bytes
        unwrap = fromRight (die "unreachable: view")
    when (isRight circuit) (view'circuit opts (unwrap circuit))
    when (isRight nilsig) (view'sig opts (unwrap nilsig))
    when (isRight ekey) $ pp (unwrap ekey) >> exit
    when (isRight vkey) $ pp (unwrap vkey) >> exit
    when (isRight proof) $ pp (unwrap proof) >> exit
    putStrLn . str'from'bytes $ bytes

view'circuit :: Opts -> Circuit Fr -> IO ()
view'circuit Opts {..} circ = do
  let View _ _ graph priv pub file = o'command
      circ'id = hex'from'bytes . sha256 . encode $ circ
  when graph $ do
    let dag = takeDirectory file ++ "/" ++ circ'id ++ ".pdf"
    export'graph dag (write'dot dot'header circ)
    unless o'quite (ok dag) >> exit
  when priv $ mapM_ putStrLn (c'privs circ) >> exit
  when pub $ mapM_ putStrLn (c'pubs circ) >> exit
  pp circ >> exit

view'sig :: Opts -> Nilsig BN254 BN254'G2 Fr G1 -> IO ()
view'sig Opts {..} sig = do
  let View hash nilkey graph priv pub file = o'command
      sig'id = hex'from'bytes . sha256 . encode $ sig
      dumper items = sort [a ++ "  -->  " ++ b | (a, b) <- items]
  when graph $ do
    let dag = takeDirectory file ++ "/" ++ sig'id ++ ".pdf"
    export'graph dag (write'dot dot'header $ n'circuit sig)
    unless o'quite (ok dag) >> exit
  when hash $
    putStrLn (hex'from'bytes . hash'sig bn254'gt $ sig) >> exit
  when nilkey $
    pp (n'key sig) >> exit
  when priv $
    mapM_ putStrLn (dumper . assocs $ which'signed sig "priv") >> exit
  when pub $
    mapM_ putStrLn (dumper . assocs $ which'signed sig "pub") >> exit
  pp sig >> exit

test :: IO ()
test = undefined

demo :: Opts -> IO ()
demo Opts {..} = do
  let Demo list item = o'command
      items = ["mpc", "zkp"]
  when list $ do
    info'io
      12
      items
      [ "multi-party computation demo using nil-sign",
        "zero-knowledge proof demo using pinocchio protocol"
      ]
    err mempty
  when (item `notElem` items) (err $ "Error, no such demo item: " ++ item)
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
        ]
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
        ]
    )
    >>= print

guard'file :: FilePath -> IO ()
guard'file file =
  unlessM (doesFileExist file) (err $ "Error, file does not exist: " ++ file)
