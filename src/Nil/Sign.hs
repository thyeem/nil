{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

-----------------------------------------------------------------------------
-- nil'sign: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

module Nil.Sign where

import Control.DeepSeq (NFData)
import Control.Monad (foldM, (<=<))
import Data.Bifunctor (bimap)
import Data.ByteString (ByteString, append)
import Data.Function (on)
import Data.List (foldl', nub)
import Data.Map (Map, delete, member)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, p'curve, toA, (~*))
import Nil.Data (NIL (NIL), lift, nil, unil)
import Nil.Eval (eval, extend'gate, extend'wire, wmap'fromList, (~~), (~~~))
import Nil.Field (Field)
import Nil.Reorg
import Nil.Utils (Pretty (..), bytes'from'str, die, ranf, sha256)
import System.Random (Random)

-- | Aggregable-signature object for nil'sign
data Nilsig i r q p = Nilsig
  { n'hash :: String,
    n'key :: Nilkey i q p,
    n'circuit :: Circuit (NIL i r q)
  }
  deriving (Eq, Show, Generic, NFData)

instance (Show q, Field q, Show p, Field p, Show r) => Pretty (Nilsig i r q p)

-- | Aggregable verification key of nilsig
type Nilkey i q p = (Point i q, Point i p)

instance
  (Show q, Pretty q, Field q, Show p, Pretty p, Field p) =>
  Pretty (Nilkey i q p)
  where
  pretty key = unlines [pretty . fst $ key, pretty . snd $ key]

-- | Initialize nil-signature
nil'init ::
  ( Integral r,
    Random r,
    Bounded r,
    Field r,
    Integral q,
    Bounded q,
    Random q,
    Field q,
    Field p
  ) =>
  Curve i q ->
  Curve i p ->
  Circuit r ->
  IO (Nilsig i r q p)
nil'init curve'q curve'p circuit = do
  phi <- ranf
  chi <- ranf
  nilified <- nilify'circuit <=< reorg'circuit $ circuit
  let omap = omap'from'gates . (extend'gate curve'q <$>) . c'gates $ nilified
      gmap = gmap'from'omap omap
      -- wmap = extend'wire curve'q <$> wmap'fromList mempty
      wmap = wmap'fromList mempty
      amps = find'amps omap
      nilkey = update'nilkey phi chi (c'g curve'q, c'g curve'p)
  gates <- foldM (backprop 1 phi gmap) omap amps -- forced initial backpropagation
  let sig = Nilsig mempty nilkey (nilified {c'gates = sort'omap gates})
  nil'sign wmap sig -- forced initial sign (constants)
{-# INLINE nil'init #-}

update'nilkey ::
  (Integral r, Field p, Field q) =>
  r ->
  r ->
  Nilkey i q p ->
  Nilkey i q p
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
    Field r,
    Field p
  ) =>
  Wmap (NIL i r q) ->
  Nilsig i r q p ->
  IO (Nilsig i r q p)
nil'sign secrets sig@Nilsig {..} = do
  alpha <- ranf
  gamma <- ranf
  let omap = omap'from'gates . c'gates $ n'circuit
      gmap = gmap'from'omap omap
      entries = find'entries omap
      amps = find'amps omap
      nilkey =
        -- randomize nilkey (key-aggregation)
        update'nilkey (recip alpha) alpha
          . update'nilkey gamma (recip gamma)
          $ n'key
  signed <- foldM (sign'gate secrets gmap) omap entries -- sign each entry
  randomized <- foldM (backprop alpha gamma gmap) signed amps -- randomize each ampgates
  let collapsed = snd . reduce $ randomized -- collapse until irreducible
  pure $
    sig
      { n'key = nilkey,
        n'hash,
        n'circuit = n'circuit {c'gates = sort'omap collapsed}
      }
{-# INLINE nil'sign #-}

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
        foldr
          (updater (recip beta))
          (foldr (updater beta) acc pasts)
          anticones
  where
    NIL c _ = w'val (g'rwire g)
    updater v = nilify False False (nil c v)
    pasts = prev'amps omap g
    anticones = nub . concat $ next'amps gmap <$> pasts
{-# INLINE backprop #-}

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
{-# INLINE nilify #-}

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

-- | Defines hash of a wire
hash'wire :: ByteString -> Omap a -> Wire a -> ByteString
hash'wire salt omap wire
  | member (w'key wire) omap =
      let (gate, _) = omap ~> w'key wire
       in hash'gate salt omap gate
  | otherwise = sha256 (bytes'from'str (w'key wire) `append` salt)
{-# INLINEABLE hash'wire #-}

-- | Defines hash of a gate
hash'gate :: ByteString -> Omap a -> Gate a -> ByteString
hash'gate salt omap Gate {..} = case g'op of
  Add -> fold $ hash'wire salt omap <$> [g'lwire, g'rwire, g'owire]
  Mul -> fold $ hash'wire salt omap <$> [g'rwire, g'owire, g'lwire]
  _ -> fold $ hash'wire salt omap <$> [g'owire, g'lwire, g'rwire]
  where
    fold = foldl' ((sha256 .) . append) mempty
{-# INLINEABLE hash'gate #-}
