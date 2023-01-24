-- | Digital Signature Algorithm (DSA) using elliptic curve cryptography
module Nil.Ecdsa where

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.Maybe (fromJust)
import Nil.Base ((~%))
import Nil.Curve
  ( Curve (..)
  , Point
  , apbq'sum
  , c'g
  , mulg
  , p'x
  )
import Nil.Ecdata
  ( Fp256k1
  , G1
  , bn128G1
  , secp256k1
  )
import Nil.Field (Field)
import Nil.Utils
  ( blake2b
  , int'from'bytes
  )
import System.Random (randomRIO)

-- | Private key (e) as a field element
type Privatekey = Integer

-- | Public key (eG) as a point on elliptic curve
type Publickey f = Point f

-- | Cryptographic hash function
type Hashfunc = ByteString -> ByteString

-- | Message to prove/verify
type Message = ByteString

-- | Signature (r, s) of Integer (field element) pair
type Signature = (Integer, Integer)

-- | ECDSA signature generation algorithm
ecdsa'sign
  :: (Eq f, Fractional f, Integral f, Field f, NFData f)
  => Curve f
  -> Hashfunc
  -> Privatekey
  -> Message
  -> IO Signature
ecdsa'sign curve hashFunc e msg = do
  let n = c'n curve
  k <- randomRIO (1, pred n)
  let r = fromIntegral . fromJust . p'x . mulg curve $ k
      z = int'from'bytes . hashFunc $ msg
      s = ((z + r * e) * (k ~% n)) `mod` n
  if s == 0 then ecdsa'sign curve hashFunc e msg else return (r, s)

-- | ECDSA verification algorithm
ecdsa'verify
  :: (Eq f, Fractional f, Integral f, Field f, NFData f)
  => Curve f
  -> Hashfunc
  -> Publickey f
  -> Signature
  -> Message
  -> Bool
ecdsa'verify curve hashFunc eG (r, s) msg
  | r < 1 || r >= n = False
  | s < 1 || s >= n = False
  | otherwise = r == r'
 where
  n = c'n curve
  r' = fromIntegral . fromJust . p'x $ apbq'sum (c'g curve, u) (eG, v)
  u = (z * (s ~% n)) `mod` n
  v = (r * (s ~% n)) `mod` n
  z = int'from'bytes . hashFunc $ msg

-- | ECDSA-sign using BN128 curve and Blake2b 32-byte hash function
bn128'sign :: Privatekey -> Message -> IO Signature
bn128'sign = ecdsa'sign bn128G1 (blake2b 32 mempty)

-- | ECDSA-verify using BN128 curve and Blake2b 32-byte hash function
bn128'verify :: Publickey G1 -> Signature -> Message -> Bool
bn128'verify = ecdsa'verify bn128G1 (blake2b 32 mempty)

-- | ECDSA-sign using secp256k1 curve and Blake2b 32-byte hash function
secp256k1'sign :: Privatekey -> Message -> IO Signature
secp256k1'sign = ecdsa'sign secp256k1 (blake2b 32 mempty)

-- | ECDSA-verify using secp256k1 curve and Blake2b 32-byte hash function
secp256k1'verify :: Publickey Fp256k1 -> Signature -> Message -> Bool
secp256k1'verify = ecdsa'verify secp256k1 (blake2b 32 mempty)
