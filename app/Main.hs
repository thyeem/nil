{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Cli
  ( Command (..)
  , Opts (..)
  , opts'parser
  )
import Control.Monad (unless, when)
import Control.Monad.Extra (unlessM)
import qualified Data.ByteString as B
import Data.Either (fromRight, isRight)
import Data.List (intercalate)
import Data.Store (PeekException, decode, encode)
import Nil
  ( BN254
  , Circuit
  , EvaluationKey
  , Fr
  , G1
  , NIL
  , Pretty (..)
  , Proof
  , VerificationKey
  , Wire (w'val)
  , Wmap
  , bn254'g1
  , compile'language
  , decode'file
  , def'curve
  , die
  , dot'header
  , err
  , export'graph
  , extend'gate
  , extend'wire
  , hex'from'bytes
  , info'io
  , qap'from'circuit
  , read'table
  , reorg'circuit
  , sha256
  , statement
  , stderr
  , str'from'bytes
  , toxicwaste
  , vec'fromWmap
  , wire'vals
  , wmap'fromList
  , write'dot
  , zkprove
  , zksetup
  , zktest
  , zkverify
  , (~>)
  )
import Options.Applicative (execParser)
import System.Directory (doesFileExist)
import System.FilePath.Posix (takeDirectory)

-- | Entry point of this program
main :: IO ()
main = execParser opts'parser >>= nil

-- | main program
nil :: Opts -> IO ()
nil opts@Opts {..} = do
  case o'command of
    Setup {} -> setup opts
    Prove {} -> prove opts
    Verify {} -> verify opts
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

  -- dump setup result (3 files: circuit, evaluation key, verification key),
  -- and their SHA-256 hashes as fingerprints
  unless o'quite $ do
    info'io
      [ "filepath"
      , "Circuit"
      , "(hash)"
      , "E-key"
      , "(hash)"
      , "V-key"
      , "(hash)" :: String
      ]
      [ path
      , file'circ
      , circ'id
      , file'ekey
      , hex'from'bytes . sha256 . encode $ ekey
      , file'vkey
      , hex'from'bytes . sha256 . encode $ vkey
      ]
  -- dump graph
  when graph $ do
    let dagfile = circ'id ++ ".pdf"
    export'graph (path ++ "/" ++ dagfile) (write'dot dot'header circuit)
    unless o'quite $ do
      putStrLn mempty
      info'io ["Graph"] [dagfile]

prove :: Opts -> IO ()
prove Opts {..} = do
  let Prove circuit ekey wit = o'command
  circuit_ <- decode'file circuit :: IO (Circuit Fr)
  ekey_ <- decode'file ekey :: IO EvaluationKey
  witness_ <- read'table wit :: IO (Wmap Fr)
  let qap = qap'from'circuit circuit_
      out = statement bn254'g1 witness_ circuit_
      vec'wit = wire'vals bn254'g1 witness_ circuit_
      proof = zkprove qap ekey_ vec'wit
      path = takeDirectory ekey
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
  proof_ <- decode'file proof :: IO Proof
  vkey_ <- decode'file vkey :: IO VerificationKey
  instance_ <- read'table inst :: IO (Wmap Fr)
  let claim = w'val $ instance_ ~> "return"
      verified = zkverify proof_ vkey_ (vec'fromWmap instance_)
  unless o'quite $ do
    info'io
      ["Statement", "Verified" :: String]
      [show (toInteger claim), show verified]

type Encoded a = Either PeekException a

view :: Opts -> IO ()
view Opts {..} = do
  let View graph reorg file = o'command
      dump :: Pretty b => Either a b -> IO ()
      dump = pp . fromRight (die "Error,")
  unlessM
    (doesFileExist file)
    (err $ "Error, file file does not exist: " ++ file)

  bytes <- B.readFile file
  let circuit = decode bytes :: Encoded (Circuit Fr)
      ekey = decode bytes :: Encoded EvaluationKey
      vkey = decode bytes :: Encoded VerificationKey
      proof = decode bytes :: Encoded Proof
  if
      | isRight circuit -> do
          let circuit_ = fromRight (die "Error,") circuit
          reorged <-
            if reorg then reorg'circuit circuit_ else pure circuit_
          if graph
            then do
              let circ'id = hex'from'bytes . sha256 . encode $ reorged
              let dagfile = circ'id ++ ".pdf"
                  path = takeDirectory file
              export'graph
                (path ++ "/" ++ dagfile)
                (write'dot dot'header reorged)
              unless o'quite $ info'io ["Graph"] [dagfile]
            else pp reorged
      | isRight ekey -> dump ekey
      | isRight vkey -> dump vkey
      | isRight proof -> dump proof
      | otherwise -> putStrLn . str'from'bytes $ bytes

test :: IO ()
test = undefined

demo :: Opts -> IO ()
demo Opts {..} = do
  let Demo list item = o'command
  when list $ stderr "francis"
  when (item == "zkp") $ demo'zkp (not o'quite)

demo'zkp :: Bool -> IO ()
demo'zkp verbose =
  zktest
    verbose
    ( intercalate
        "\n\t"
        [ "language (priv e, priv r, priv s, pub z)"
        , "let k = (z + r * e) / s"
        , "let P = [e]"
        , "let R = [k]"
        , "let o = if (:R - r) == 0 then :P else :R"
        , "return o"
        ]
    )
    ( wmap'fromList
        [
          ( "e"
          , 8464813805670834410435113564993955236359239915934467825032129101731355555480
          )
        ,
          ( "r"
          , 13405614924655214385005113554925375156635891943694728320775177413191146574283
          )
        ,
          ( "s"
          , 13078933289364958062289426192340813952257377699664878821853496586753686181509
          )
        ,
          ( "z"
          , 4025919241471660438673811488519877818316526842848831811191175453074037299584
          )
        ]
        :: Wmap Fr
    )
    ( wmap'fromList
        [
          ( "return"
          , 20546328083791890245710917085664594543309426573230401055874323960053340664311
          )
        ,
          ( "z"
          , 4025919241471660438673811488519877818316526842848831811191175453074037299584
          )
        ]
    )
    >>= print
