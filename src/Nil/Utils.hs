{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Nil.Utils where

import Control.DeepSeq
  ( NFData,
    deepseq,
  )
import Control.Monad ((>=>))
import Control.Parallel
  ( par,
    pseq,
  )
import qualified Crypto.Hash.BLAKE2.BLAKE2b as B2b
import qualified Crypto.Hash.SHA256 as S256
import qualified Crypto.Hash.SHA512 as S512
import Data.Bifunctor (bimap)
import Data.Bits (Bits (..))
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as H
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Char8 as CL
import Data.Char (isSpace)
import Data.Function (on)
import Data.List
  ( dropWhileEnd,
    foldl',
    intercalate,
    isPrefixOf,
    unfoldr,
  )
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Word (Word8)
import Numeric (showHex)
import System.Entropy (getEntropy)
import System.Exit (exitFailure, exitSuccess)
import qualified System.IO
import System.Random (Random, randomRIO)
import Text.Pretty.Simple
  ( OutputOptions (..),
    StringOutputStyle (..),
    pShowOpt,
  )
import Text.Printf (printf)

type Text = T.Text

type ByteString = C.ByteString

type LazyText = TL.Text

type LazyByteString = CL.ByteString

-- | Pretty-Show and Pretty-Printer
class (Show a) => Pretty a where
  pretty :: a -> String
  pretty = TL.unpack . pShowOpt option
    where
      option =
        OutputOptions
          { outputOptionsIndentAmount = 4,
            outputOptionsPageWidth = 0,
            outputOptionsCompact = False,
            outputOptionsCompactParens = True,
            outputOptionsInitialIndent = 0,
            outputOptionsColorOptions = Nothing,
            outputOptionsStringStyle = EscapeNonPrintable
          }
  pp :: a -> IO ()
  pp = putStrLn . pretty

deriving instance Pretty Integer

deriving instance Pretty Bool

deriving instance Pretty Char

deriving instance Pretty ()

deriving instance Pretty Text

deriving instance Pretty ByteString

deriving instance Pretty LazyText

deriving instance Pretty LazyByteString

-- | Parallel computing (+) operator
(|+|) :: (Num a) => a -> a -> a
a |+| b = a `par` b `pseq` a + b
{-# INLINE (|+|) #-}

-- | Parallel computing (-) operator
(|-|) :: (Num a) => a -> a -> a
a |-| b = a `par` b `pseq` a - b
{-# INLINE (|-|) #-}

-- | Parallel computing (*) operator
(|*|) :: (Num a) => a -> a -> a
a |*| b = a `par` b `pseq` a * b
{-# INLINE (|*|) #-}

-- | Parallel computing (/) operator
(|/|) :: (Fractional a) => a -> a -> a
a |/| b = a `par` b `pseq` a / b
{-# INLINE (|/|) #-}

-- | Parallel computing (==) operator
(|=|) :: (Eq a) => a -> a -> Bool
a |=| b = a `par` b `pseq` a == b
{-# INLINE (|=|) #-}

-- | Parallel computing (&&) operator
(|&|) :: Bool -> Bool -> Bool
a |&| b = a `par` b `pseq` a && b
{-# INLINE (|&|) #-}

-- | Parallel computing (||) operator
(|||) :: Bool -> Bool -> Bool
a ||| b = a `par` b `pseq` a || b
{-# INLINE (|||) #-}

-- | Need to use 'deepseq' inside a 'par' here
-- deep x == id $!! x
deep :: (NFData a) => a -> a
deep a = a `deepseq` a
{-# INLINE deep #-}

-- | Infix pmap
(<%>) :: (NFData a, NFData b) => (a -> b) -> [a] -> [b]
(<%>) = pmap
{-# INLINE (<%>) #-}

infixl 4 <%>

-- | Parallel map using deepseq, par and pseq
pmap :: (NFData a, NFData b) => (a -> b) -> [a] -> [b]
pmap _ [] = []
pmap f (x : xs) = y `par` ys `pseq` (y : ys)
  where
    y = deep $ f x
    ys = pmap f xs
{-# INLINE pmap #-}

-- | Parallel zipWith using deepseq, par and pseq
pzip'with ::
  (NFData a, NFData b, NFData c) => (a -> b -> c) -> [a] -> [b] -> [c]
pzip'with f = g
  where
    g [] _ = []
    g _ [] = []
    g (x : xs) (y : ys) = z `par` zs `pseq` (z : zs)
      where
        z = deep $ f x y
        zs = g xs ys
{-# INLINE pzip'with #-}

-- | Parallel folding using par and pseq
-- For any associative binary operator f and monoid a
pfold :: (Monoid a) => (a -> a -> a) -> [a] -> a
pfold _ [x] = x
pfold f xs = as `par` bs `pseq` f as bs
  where
    as = pfold f as'
    bs = pfold f bs'
    (as', bs') = splitAt (length xs `div` 2) xs
{-# INLINE pfold #-}

-- | Sequencing IO actions in parallel
pthenIO :: (Monad m) => m a -> m b -> m b
pthenIO ma mb = ma `par` mb `pseq` (ma *> mb)
{-# INLINE pthenIO #-}

-- | Strict foldM
foldM' :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldM' _ z [] = pure z
foldM' f z (x : xs) = do
  z' <- f z x
  z' `seq` foldM' f z' xs
{-# INLINE foldM' #-}

-- | Map a function over a 2-element tuple
tmap :: (a -> b) -> (a, a) -> (b, b)
tmap = uncurry . on (,)
{-# INLINE tmap #-}

-- | Elementwise binary operation with two 2-element tuples
tbop :: (a -> a -> b) -> (a, a) -> (a, a) -> (b, b)
tbop op x = uncurry bimap (tmap op x)
{-# INLINE tbop #-}

-- | Explicitly convert [u8] into bytes
bytes'from'u8 :: [Word8] -> B.ByteString
bytes'from'u8 = B.pack

u8'from'bytes :: B.ByteString -> [Word8]
u8'from'bytes = B.unpack

-- | Explicitly convert [u8] into string
str'from'u8 :: [Word8] -> String
str'from'u8 = str'from'bytes . bytes'from'u8

u8'from'str :: String -> [Word8]
u8'from'str = u8'from'bytes . bytes'from'str

-- | Explicitly convert string into bytes
bytes'from'str :: String -> B.ByteString
bytes'from'str = C.pack

-- | Explicitly convert bytes into string
str'from'bytes :: B.ByteString -> String
str'from'bytes = C.unpack

-- | Explicitly convert lazy bytes into string
str'from'lbytes :: L.ByteString -> String
str'from'lbytes = str'from'bytes . L.toStrict

lbytes'from'str :: String -> L.ByteString
lbytes'from'str = L.fromStrict . bytes'from'str

int'from'u8 :: [Word8] -> Integer
int'from'u8 = foldr unstep 0
  where
    unstep b a = a `shiftL` 8 .|. fromIntegral b

u8'from'int :: Integer -> [Word8]
u8'from'int x = unfoldr step (abs x)
  where
    step 0 = Nothing
    step i = Just (fromIntegral i, i `shiftR` 8)

bytes'from'int :: Integer -> B.ByteString
bytes'from'int = bytes'from'u8 . u8'from'int

int'from'bytes :: B.ByteString -> Integer
int'from'bytes = int'from'u8 . u8'from'bytes

-- | Explicitly convert integer into string
str'from'int :: Integer -> String
str'from'int = str'from'u8 . u8'from'int

int'from'str :: String -> Integer
int'from'str = int'from'u8 . u8'from'str

bytes'from'hex :: String -> B.ByteString
bytes'from'hex = H.decodeLenient . bytes'from'str . unwrap
  where
    unwrap x = if take 2 x == "0x" then drop 2 x else x

hex'from'bytes :: B.ByteString -> String
hex'from'bytes = str'from'bytes . H.encode

int'from'hex :: String -> Integer
int'from'hex hexstring = read $ unwrap hexstring :: Integer
  where
    unwrap x = if take 2 x == "0x" then x else "0x" <> x

hex'from'int :: Integer -> String
hex'from'int x = showHex x ""

bits'from'int :: Integer -> [Integer]
bits'from'int x = (1 .&.) . (x `shiftR`) <$> [0 .. n]
  where
    n = (floor @Float) . logBase 2 $ fromIntegral x

-- | Get fixed-length-of-big-endian-bytes from a given integer
bytes'from'int' :: Int -> Integer -> B.ByteString
bytes'from'int' len x
  | diff > 0 = (B.concat . replicate diff $ nul) <> bytes
  | otherwise = bytes
  where
    bytes = bytes'from'int x
    nul = bytes'from'str "\NUL"
    diff = len - B.length bytes

base64'from'bytes :: B.ByteString -> String
base64'from'bytes = str'from'bytes . B64.encode

bytes'from'base64 :: String -> B.ByteString
bytes'from'base64 = B64.decodeLenient . bytes'from'str

random'bytes :: Int -> IO B.ByteString
random'bytes = getEntropy

-- | Generate random hex string of given length
random'hex :: Int -> IO String
random'hex = random'bytes >=> pure . hex'from'bytes

-- | Get a message digest of FILE using a given hasher
filehex :: (B.ByteString -> B.ByteString) -> FilePath -> IO String
filehex hasher file = hex'from'bytes . hasher <$> B.readFile file

-- | Zip with a binary op, a default value and the longest list.
lzip'with :: (a -> a -> a) -> a -> [a] -> [a] -> [a]
lzip'with op def = go
  where
    go r@(_ : _) [] = flip op def <$> r
    go [] r@(_ : _) = op def <$> r
    go [] [] = []
    go (x : xs) (y : ys) = op x y : go xs ys
{-# INLINE lzip'with #-}

-- | Generate a random element except for additive/multiplicative identity
ranf :: (Num f, Random f, Bounded f) => IO f
ranf = randomRIO (minBound + 2, maxBound - 1)

-- | Random sampling of k from [p]
sample :: [p] -> Int -> IO [p]
sample xs n
  | n < 0 = die $ "Error, non-positive sample size: " ++ show n
  | otherwise = f xs []
  where
    f [] acc = pure acc
    f xs' acc
      | length acc >= n = pure acc
      | otherwise = do
          k <- randomRIO (0, length xs' - 1)
          case splitAt k xs' of
            (a, b : bs) -> f (bs <> a) (b : acc)
            _ -> die "Error, sampling"

-- | Shuffle a given list
shuffle :: [p] -> IO [p]
shuffle xs = sample xs (length xs)

-- | Raise error without annoying stacktrace
die :: String -> a
die = errorWithoutStackTrace

-- | Print to stdout (hPutStrLn stdout)
stdout :: String -> IO ()
stdout = putStrLn

-- | Print to stderr
stderr :: String -> IO ()
stderr = System.IO.hPutStrLn System.IO.stderr

-- | stdout and exit(0)
ok :: String -> IO ()
ok msg = stdout msg >> exitSuccess

-- | stdout and exit(1)
err :: String -> IO ()
err msg = stderr msg >> exitFailure

-- | print each of [a] on a separate line
prints :: (Show a) => [a] -> IO ()
prints = mapM_ print

-- | The same as prints, but with line numbers
nprints :: (Show a) => [a] -> IO ()
nprints xs =
  mapM_
    putStrLn
    [printf "%4s  %s" (show n) (show x) | n <- [1 :: Int ..] | x <- xs]

-- | Peel off line feed and blanks at rightmost
rstrip :: String -> String
rstrip = dropWhileEnd isSpace

-- | Peel off blanks at leftmost
lstrip :: String -> String
lstrip = dropWhile isSpace

-- | Peel off blanks at both sides
strip :: String -> String
strip = lstrip . rstrip

-- | The same as takeWhile but take one more just before quitting loop
takeWhile' :: (a -> Bool) -> [a] -> [a]
takeWhile' p = foldl' (\acc x -> if p x then x : acc else [x]) []

-- | Slice a given list between i and j: [i, j] closed set
-- Index starts from 0
slice :: [a] -> (Int, Int) -> [a]
slice xs (i, j) = [x | (x, k) <- zip xs [0 .. j], i <= k]
{-# INLINE slice #-}

-- | Split [a] into [[a]] using given delimiter [a]
splitby :: (Eq a) => [a] -> [a] -> [[a]]
splitby [] _ = []
splitby block delim = go [[]] block
  where
    go a [] = reverse a
    go a@(x : xs) b@(y : ys)
      | delim `isPrefixOf` b = go ([] : a) (drop (length delim) b)
      | otherwise = go ((x <> [y]) : xs) ys
    go _ _ = die "unreachable. broken function: splitby"
{-# INLINE splitby #-}

-- | Replace old string a with a new string b over a given list
replace :: (Eq a) => [a] -> [a] -> [a] -> [a]
replace old new = intercalate new . flip splitby old
{-# INLINE replace #-}

-- | Split a list into n-length lists
chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = let (o, rest) = splitAt n xs in o : chunks n rest
{-# INLINE chunks #-}

-- | Control flow using guard: conditional identity function
assert :: Bool -> a -> a
assert True = id
assert False = const (die "Assertion Failed")

-- | Check if balanced for a given string including any parenthesis-like symbol
isbalanced :: Char -> Char -> String -> Bool
isbalanced bra ket xs
  | check = True
  | otherwise = False
  where
    f x
      | x == bra = 1 :: Int
      | x == ket = -1
      | otherwise = 0
    g = f <$> xs
    check = sum g == 0 && all (>= 0) (scanl (+) 0 g)

-- | Blake2b Hash function
blake2b :: Int -> B.ByteString -> B.ByteString -> B.ByteString
blake2b = B2b.hash
{-# INLINE blake2b #-}

-- | Blake2b for Integer -> Integer
blake2b'integer :: Int -> Integer -> Integer
blake2b'integer size = int'from'bytes . blake2b size mempty . bytes'from'int
{-# INLINE blake2b'integer #-}

-- | SHA256 Hash function
sha256 :: B.ByteString -> B.ByteString
sha256 = S256.hash
{-# INLINE sha256 #-}

-- | SHA256 for Integer -> Integer
sha256'integer :: Integer -> Integer
sha256'integer = int'from'bytes . sha256 . bytes'from'int
{-# INLINE sha256'integer #-}

-- | SHA512 Hash function
sha512 :: B.ByteString -> B.ByteString
sha512 = S512.hash
{-# INLINE sha512 #-}

-- | SHA512 for Integer -> Integer
sha512'integer :: Integer -> Integer
sha512'integer = int'from'bytes . sha512 . bytes'from'int
{-# INLINE sha512'integer #-}

-- | Construct two-columns formatted table.
-- No need two lists have the same length as the default value will be filled
twocols :: String -> String -> [String] -> [String] -> String
twocols def fmt a b =
  intercalate "\n" $ lzip'with (printf fmt) def a b
{-# INLINE twocols #-}

-- | info
info :: [String] -> [String] -> String
info = twocols mempty "%12s    %s"
{-# INLINE info #-}

-- | Default formatted printer of this project
info'io :: [String] -> [String] -> IO ()
info'io = (stderr .) . info
{-# INLINE info'io #-}
