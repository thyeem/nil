{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- nil'sign: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

module Nil.Sign where

import Control.DeepSeq (NFData)
import Control.Monad (unless, when, (<=<))
import Control.Parallel (par, pseq)
import Data.Bifunctor (bimap)
import Data.ByteString (ByteString, append)
import Data.Function (on)
import Data.List (find, foldl', nub, sort)
import Data.Map (Map, delete, member)
import Data.Store (Store)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, p'curve, toA, (~*))
import Nil.Data (NIL (NIL), UL, lift, nil, unil, unil')
import Nil.Ecdata (BN254, BN254'G2, Fr, G1, bn254'g1, bn254'g2, bn254'gt)
import Nil.Eval
  ( eval,
    eval'circuit,
    extend'gate,
    extend'wire,
    statement,
    wmap'fromList,
    (~~),
    (~~~),
  )
import Nil.Field (Extensionfield (..), Field, unef)
import Nil.Pairing (pairing)
import Nil.Reorg
import Nil.Utils
  ( Pretty (..),
    bytes'from'hex,
    bytes'from'int,
    bytes'from'str,
    deep,
    die,
    foldM',
    hex'from'bytes,
    ranf,
    sha256,
    stderr,
    (<%>),
    (|=|),
  )
import System.Random (Random)

-- | Aggregable-signature object for nil'sign
data Nilsig i j r q = Nilsig
  { n'key :: Nilkey i j q,
    n'circuit :: Circuit (NIL i r q)
  }
  deriving (Eq, Show, Generic, NFData)

deriving instance Store (Nilsig BN254 BN254'G2 Fr G1)

instance (Show q, Field q, Show r) => Pretty (Nilsig i j r q)

-- | Aggregable verification key of nilsig
type Nilkey i j q = (Point i q, Point j (Extensionfield q j))

instance
  (Show q, Pretty q, Field q) =>
  Pretty (Nilkey i j q)
  where
  pretty key = unlines [mempty, pretty . fst $ key, pretty . snd $ key]

-- | Initialize nil-signature
nil'init ::
  ( Integral r,
    Random r,
    Bounded r,
    Field r,
    Integral q,
    Bounded q,
    Random q,
    Field q
  ) =>
  Curve i q ->
  Curve j (Extensionfield q j) ->
  Curve t (Extensionfield q t) ->
  Circuit r ->
  IO (Nilsig i j r q)
nil'init curve'g1 curve'g2 curve'gt circuit = do
  phi <- ranf
  chi <- ranf
  nilified <- nilify'circuit <=< reorg'circuit $ circuit
  let omap = omap'from'gates . (extend'gate curve'g1 <$>) . c'gates $ nilified
      gmap = gmap'from'omap omap
      wmap = wmap'fromList mempty
      amps = find'amps omap
      nilkey = update'nilkey phi chi (c'g curve'g1, c'g curve'g2)
  gates <-
    foldM' (backprop 1 phi gmap) omap amps -- forced initial backpropagation
  let sig = Nilsig nilkey (nilified {c'gates = sort'omap gates})
  nil'sign curve'gt wmap sig -- forced initial sign (constants)
{-# INLINE nil'init #-}

update'nilkey ::
  (Integral r, Field q) =>
  r ->
  r ->
  Nilkey i j q ->
  Nilkey i j q
update'nilkey a b = bimap (~* a) (~* b)
{-# INLINE update'nilkey #-}

-- | Nilsign: homomorphically ecrypt secrets based on a reorged circuit.
-- Here, @sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets.
nil'sign ::
  ( Field q,
    Bounded q,
    Random q,
    Integral q,
    Integral r,
    Random r,
    Bounded r,
    Field r
  ) =>
  Curve t (Extensionfield q t) ->
  Wmap (NIL i r q) ->
  Nilsig i j r q ->
  IO (Nilsig i j r q)
nil'sign curve secrets sig@Nilsig {..} = do
  alpha <- ranf
  gamma <- ranf
  let omap = omap'from'gates . c'gates $ n'circuit
      gmap = gmap'from'omap omap
      amps = find'amps omap
      entries = find'entries omap
      nilkey =
        update'nilkey (recip alpha) alpha
          . update'nilkey gamma (recip gamma)
          $ n'key -- randomize nilkey (key-aggregation)
  signed <-
    foldM' (sign'gate secrets gmap) omap entries -- sign each entry
  randomized <- foldM' (backprop alpha gamma gmap) signed amps -- randomize each ampgates
  let collapsed = snd . reduce $ randomized -- collapse until irreducible
  pure $ sig {n'key = nilkey, n'circuit = n'circuit {c'gates = sort'omap collapsed}}
{-# INLINEABLE nil'sign #-}

-- | Randomize the end amp and backpropagate to the other amps
backprop ::
  (Integral q, Field q, Random r, Bounded r, Integral r, Field r) =>
  r ->
  r ->
  Gmap (NIL i r q) ->
  Omap (NIL i r q) ->
  Gate (NIL i r q) ->
  IO (Omap (NIL i r q))
backprop alpha gamma gmap omap g
  | entry'amp'p omap g = pure $ updater (recip alpha) g omap
  | otherwise = do
      beta <- ranf
      let acc = if prin'amp'p omap g then updater gamma g omap else omap
      pure $
        foldl'
          (flip (updater (recip beta)))
          (foldl' (flip (updater beta)) acc pasts)
          anticones
  where
    NIL c _ = w'val (g'rwire g)
    updater v = nilify False False (nil c v)
    pasts = prev'amps omap g
    anticones = nub $ concatMap (next'amps gmap) pasts
{-# INLINEABLE backprop #-}

-- | Sign each entry gate assigned for a signer
sign'gate ::
  (Random r, Bounded r, Integral r, Integral q, Field r, Field q) =>
  Wmap (NIL i r q) ->
  Gmap (NIL i r q) ->
  Omap (NIL i r q) ->
  Gate (NIL i r q) ->
  IO (Omap (NIL i r q))
sign'gate secrets gmap omap g = do
  delta <- ranf
  epsilon <- ranf
  let (entry, other) = either'by entry'wirep g
      NIL c _ = w'val entry
  if member (w'key entry) secrets
    then do
      let lifter = if g'op g == Add then lift else id
          secret = secrets ~~ entry
          multiplier = nil c $ recip delta
          unshifter = lifter . nil c $ -delta * epsilon
          shifted
            | const'wirep entry = nil c delta * (nil c 1 + nil c epsilon / secret)
            | otherwise = nil c delta * (secret + nil c epsilon)
       in pure
            . nilify False False multiplier (get'amp gmap g)
            . nilify False True unshifter (get'shifter omap gmap g)
            . nilify True True shifted g
            $ omap
    else pure omap
{-# INLINEABLE sign'gate #-}

-- | Tamper the unlifted value of gates and mix them with random numbers
nilify ::
  (Integral r, Integral q, Field r, Field q) =>
  Bool -> -- which side to update? lwire -> True, rwire: False
  Bool -> -- the wire to be frozen?
  NIL i r q ->
  Gate (NIL i r q) ->
  Omap (NIL i r q) ->
  Omap (NIL i r q)
nilify leftp closep val g omap =
  let gate@Gate {g'lwire = gl, g'rwire = gr} = omap >>> g
      finish = if closep then freeze . set'recip False else set'recip False
      gate' =
        if leftp
          then gate {g'lwire = finish $ val ~~~ gl}
          else gate {g'rwire = finish $ val ~~~ gr}
   in omap <<< gate'
{-# INLINEABLE nilify #-}

-- | Further collapse gates from entries if reducible
reduce :: (Eq a, Fractional a) => Omap a -> (Wmap a, Omap a)
reduce o = foldl' update (mempty, o) (sort'omap o)
  where
    update (wmap, omap) gate@Gate {..} =
      let g = gate {g'lwire = rep g'lwire, g'rwire = rep g'rwire}
          rep wire
            | member (w'key wire) wmap = wmap ~~> wire
            | otherwise = wire
       in if reducible g
            then
              ( wmap <~ (w'key g'owire, freeze . val'const $ eval' g),
                delete (w'key g'owire) omap
              )
            else (wmap, omap <<< g)
    reducible g = and' const'wirep g && nor' amp'wirep g && nor' shift'wirep g
    eval' Gate {..} = on op w'val g'lwire g'rwire
      where
        op = case g'op of
          Mul -> (*)
          Add -> (+)
          a -> die $ "Error, not evaluable operator: " ++ show a
{-# INLINEABLE reduce #-}

-- | nil check
nil'check ::
  (Integral r, Integral q, Field r, Field q) =>
  Curve t (Extensionfield q t) ->
  r ->
  Nilsig i j r q ->
  Bool
nil'check curve fval sig@Nilsig {..}
  | not . null $ entries =
      die $
        "Error, used Nilsig not fully signed yet: "
          ++ show (nub . w'key . g'lwire <$> entries)
  | otherwise = pairing curve out chi |=| (pairing curve phi chi ^ fval)
  where
    omap = omap'from'gates . c'gates $ n'circuit
    entries = find'entries omap
    wmap = extend'wire (p'curve phi) <$> wmap'fromList [(return'key, fval)]
    out = unil' . w'val $ eval'circuit wmap n'circuit ~> return'key
    (phi, chi) = n'key
{-# INLINEABLE nil'check #-}

hash'sig ::
  (Field q, Integral q, Integral r, Field r) =>
  Curve t (Extensionfield q t) ->
  Nilsig i j r q ->
  ByteString
hash'sig curve sig@Nilsig {..} =
  nilkey `par`
    amps `pseq`
      sha256 (nilkey `append` amps)
  where
    nilkey = deep $ hash'nilkey curve n'key
    amps = deep $ hash'amps omap
    omap = omap'from'gates . c'gates $ n'circuit
{-# INLINEABLE hash'sig #-}

-- | Defines hash-value of sig-circuit-gates
hash'amps ::
  (Eq q, Field r, Integral r, Integral q, Field q) =>
  Omap (NIL i r q) ->
  ByteString
hash'amps omap =
  foldl'
    ((sha256 .) . append)
    salt
    (bytes'from'str . w'key . g'owire <%> sort (find'amps omap))
  where
    amps = sort (find'amps omap)
    salt = case find (prin'amp'p omap) amps of
      Just amp -> bytes'from'int . toInteger . unil . w'val . g'owire $ amp
      _ -> die "Error, cannot evaluate hash of Nilsig: no principal amp"
{-# INLINEABLE hash'amps #-}

hash'nilkey ::
  (Field q, Integral q) =>
  Curve t (Extensionfield q t) ->
  Nilkey i j q ->
  ByteString
hash'nilkey curve (phi, chi) =
  foldl'
    ((sha256 .) . append)
    mempty
    (bytes'from'int . toInteger <$> lambda)
  where
    lambda = unef $ pairing curve phi chi
{-# INLINEABLE hash'nilkey #-}

verify'hash ::
  (Field q, Integral q, Integral r, Field r) =>
  Curve t (Extensionfield q t) ->
  Nilsig i j r q ->
  String ->
  Bool
verify'hash curve sig@Nilsig {..} hex = hash'sig curve sig == bytes'from'hex hex
{-# INLINE verify'hash #-}

nil'test :: Bool -> String -> Wmap Fr -> IO Bool
nil'test verbose language wmap = do
  -- Language
  when verbose $ do
    stderr mempty
    stderr language
  let circuit = compile'language language

  -- initial signature
  sig <- nil'init bn254'g1 bn254'g2 bn254'gt circuit
  when verbose $ do
    stderr mempty
    stderr "Initializing nil-signature..."
    stderr $ "(hash) " ++ hex'from'bytes (hash'sig bn254'gt sig)
    stderr (pretty sig)

  -- signeds signature
  signed <- nil'sign bn254'gt (extend'wire bn254'g1 <$> wmap) sig
  when verbose $ do
    stderr mempty
    stderr "Signing nil-signature..."
    stderr $ "(hash) " ++ hex'from'bytes (hash'sig bn254'gt signed)
    stderr (pretty signed)

  -- expected return: f(Wij)
  let fval = statement bn254'g1 wmap circuit
  let ret = w'val $ wmap ~> return'key
  let verified = nil'check bn254'gt ret signed
  when verbose $ do
    stderr mempty
    stderr "Checking validity of nil-signature..."
    stderr $ "    Given f-value: " ++ show ret
    stderr $ "Evaluated f-value: " ++ show fval
    stderr $ "Verified: " ++ show verified
  pure verified
