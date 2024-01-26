{-# LANGUAGE DataKinds #-}

module Nil.Shamir
  ( Shares
  , sss'encode
  , sss'decode
  ) where

import           Nil.Field ( Primefield (..), pf )
import           Nil.Poly  ( evalLagrangepoly', (|=), (|?) )
import           Nil.Utils ( bytes'from'int, bytes'from'str, die,
                             int'from'bytes, str'from'bytes )

-- | Field of Secret: maxinum length of secret
-- Maximum length of available secret depends on the size of prime used.
-- Simply choose like secp256k1 curve char = 2^256 - 2^32 - 977, Fp, as shown above
-- Or use Fm above for encoding much longer secret.
-- Mersenne primes, where p = {..,127, 521, 607, 1279, 2203,..} then fp = 2^p - 1
-- Here used Mersenne prime when p = 1279, then 386 digits of fp can encode almost 160 bytes.
type Fp
   = Primefield 115792089237316195423570985008687907853269984665640564039457584007908834671663

type Shares = [(Fp, Fp)]

-- | Encode a given string of secret and then generate Shares, [(p, p)]
-- where n [total number of token] and k [threshold of tokens required for decoding]
-- More than or equal to 'k tokens' required to decode the fractured secret.
sss'encode :: String -> Int -> Int -> IO Shares
sss'encode secret n k
  | intercept >= limit = ioError $ userError "Secret is too long"
  | n <= 0 || k <= 0 = ioError $ userError "n and k must be positive"
  | n < k = ioError $ userError "k cannot be greater than n"
  | otherwise = do
    coeffs <- (1, limit) |? (k - 1)
    let poly = pf intercept : coeffs
    return $ (\x -> (,) x (poly |= x)) . fromIntegral <$> [1 .. n]
  where
    intercept = int'from'bytes . bytes'from'str $ secret
    limit = toInteger (maxBound :: Fp)

-- | Recover the secret from the Shares
sss'decode :: Shares -> String
sss'decode [] = die "Nothing to decode"
sss'decode share =
  str'from'bytes . bytes'from'int . toInteger $ evalLagrangepoly' share 0
