{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

-----------------------------------------------------------------------------
-- nilsign: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

module Nil.Sign where

import Control.DeepSeq (NFData)
import Control.Monad (foldM, (<=<))
import Data.ByteString (ByteString, append)
import Data.List (foldl', nub, sortOn)
import Data.Map (Map, assocs, elems, member)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, p'curve, toA, (~*))
import Nil.Data (NIL (NIL), lift, nil, unil, unitp)
import Nil.Eval (extend'gate, extend'wire)
import Nil.Field (Field)
import Nil.Reorg
  ( Omap
  , amp'wirep
  , either'by
  , entry'wirep
  , freeze
  , nilify'circuit
  , omap'from'gates
  , reorg'circuit
  , shift'wirep
  , xor'
  )
import Nil.Utils (Pretty (..), bytes'from'str, die, ranf, sha256)
import System.Random (Random)

-- | Aggregable-signature object for nilsign
data Nilsig i r q p = Nilsig
  { nil'hash :: String
  , nil'key :: Nilkey i q p
  , nil'circuit :: Circuit (NIL i r q)
  }
  deriving (Eq, Show, Generic, NFData)

-- instance (Show q, Field q, Show p, Field p, Show r) => Pretty (Nilsig i r q p)

-- | Aggregable verification key of nilsig
type Nilkey i q p = (Point i q, Point i p)

instance
  (Show q, Pretty q, Field q, Show p, Pretty p, Field p)
  => Pretty (Nilkey i q p)
  where
  pretty key = unlines [pretty . fst $ key, pretty . snd $ key]

-- | Map describing a circuit as DAG
type Gmap a = Map String [Gate a]

{- | Put an edge record to the graph-map
 key -> out-wire of [FROM gate]
 gate -> [TO gate]
-}
(<<~) :: Eq a => Gmap a -> (String, Gate a) -> Gmap a
(<<~) gmap (key, gate)
  | member key gmap =
      let gates = gmap ~> key
       in gmap <~ (key, nub $ gate : gates)
  | otherwise = gmap <~ (key, [gate])
{-# INLINE (<<~) #-}

-- | Follow a wire to traverse graph
(~>>) :: Gmap a -> String -> [Gate a]
(~>>) gmap key
  | member key gmap = gmap ~> key
  | otherwise = die $ "Error, not found wire-key or reached a deadend: " ++ key

-- | Overwrite/replace previous gate with the new evaluated one
(<<<) :: Eq a => Omap a -> Gate a -> Omap a
(<<<) omap gate@Gate {g'owire = Wire {w'key}}
  | member w'key omap =
      let (_, height) = omap ~> w'key
       in omap <~ (w'key, (gate, height))
  | otherwise = die $ "Error, not found gate-key: " ++ w'key
{-# INLINE (<<<) #-}

-- | Eval nil-signature
verify'sig :: Nilsig i r q p -> Wmap (NIL i r q) -> Wire (NIL i r q)
verify'sig Nilsig {..} pubs = undefined

-- | Initialize nil-signature
init'sig
  :: ( Integral q
     , Field q
     , Field p
     , Integral r
     , Random r
     , Bounded r
     )
  => Curve i q
  -> Curve i p
  -> Circuit r
  -> IO (Nilsig i r q p)
init'sig curve'q curve'p circuit = do
  phi <- ranf
  chi <- ranf
  nilified <- nilify'circuit <=< reorg'circuit $ circuit
  let gates = extend'gate curve'q <$> c'gates nilified
      _ = phi * chi * (unil . w'val . g'owire . last $ gates)
  pure $
    Nilsig
      mempty
      (c'g curve'q ~* phi, c'g curve'p ~* chi)
      (nilified {c'gates = gates})
{-# INLINE init'sig #-}

{- | Nilsign: homomorphically ecrypt secrets based on a reorged circuit.
 Here, @sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets.
-}
nilsign
  :: ( Field q
     , Bounded q
     , Random q
     , Integral q
     , Eq r
     , Integral r
     , Field p
     , Random r
     , Bounded r
     , Field r
     )
  => Nilsig i r q p
  -> Wmap r
  -> IO (Nilsig i r q p)
nilsign
  sig@Nilsig {nil'key = (phi'p, chi'p), ..}
  secrets = do
    gamma <- ranf
    let c = p'curve phi'p
        wmap = extend'wire c <$> secrets
        omap = omap'from'gates . c'gates $ nil'circuit
        gmap = gmap'from'omap omap
    signed <- foldM (sign'gate wmap gmap) omap (find'entries omap)
    done <- foldM (update'phi gamma) signed (find'amps signed)
    pure $
      sig
        { nil'key =
            ( toA $ phi'p ~* gamma
            , toA $ chi'p ~* recip gamma
            )
        , nil'hash
        , nil'circuit =
            nil'circuit {c'gates = (fst <$>) . sortOn snd . elems $ done}
        }
{-# INLINE nilsign #-}

gmap'from'omap :: Eq a => Omap a -> Gmap a
gmap'from'omap omap =
  let gates = fst <$> sortOn (negate . snd) (elems omap)
      go'wire gate gmap wire
        | out'wirep wire = gmap <<~ (w'key wire, gate)
        | otherwise = gmap
      update gmap gate@Gate {..} =
        foldl' (go'wire gate) gmap [g'lwire, g'rwire]
   in foldl' update mempty gates
{-# INLINEABLE gmap'from'omap #-}

-- | Find a list of entry gates
find'entries :: Omap a -> [Gate a]
find'entries omap =
  [g | (g, _) <- elems omap, g'op g /= End, xor' entry'wirep g]
{-# INLINE find'entries #-}

-- | Find a list of amplifier gates
find'amps :: Omap a -> [Gate a]
find'amps omap = foldl' go [] (assocs omap)
 where
  go gates (_, (gate, _))
    | xor' amp'wirep gate = gate : gates
    | otherwise = gates
{-# INLINE find'amps #-}

-- | Global update of phi for each principal amplifiers
update'phi
  :: (Integral q, Field q, Random r, Bounded r, Integral r, Field r)
  => r
  -> Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> IO (Omap (NIL i r q))
update'phi gamma omap g@Gate {..}
  | prin'amp'p omap g = do
      let (NIL c _) = w'val g'rwire
          val = w'val g'rwire * nil c gamma
          rwire = g'rwire {w'val = val}
      pure $ omap <<< g {g'rwire = rwire}
  | otherwise = backprop'beta omap g
{-# INLINE update'phi #-}

-- | Update non-principal amp with random beta and then backpropagate it
backprop'beta
  :: (Integral q, Field q, Random r, Bounded r, Integral r, Field r)
  => Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> IO (Omap (NIL i r q))
backprop'beta omap g = do
  beta <- ranf
  let (NIL c _) = w'val (g'rwire g)
      amps = prev'amps omap g
      update rand m Gate {..} =
        let val = w'val g'rwire * nil c rand
            rwire = g'rwire {w'val = val}
         in m <<< g {g'rwire = rwire}
  pure $ foldl' (update (recip beta)) (update beta omap g) amps
{-# INLINE backprop'beta #-}

-- | Sign each entry gate assigned for a signer
sign'gate
  :: (Random r, Bounded r, Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> IO (Omap (NIL i r q))
sign'gate wmap gmap omap g@Gate {..} = do
  delta <- ranf
  epsilon <- ranf
  let (entry, other) = either'by entry'wirep g
      entry'val@(NIL c _) = w'val entry
      owner'p = member (w'key entry) wmap && not (const'wirep entry)
      tampered'p = not . unitp . w'val $ entry
      sigma =
        if owner'p
          then entry'val * (nil c delta * (w'val (wmap ~~> entry) + nil c epsilon))
          else nil c delta * (entry'val + nil c epsilon)
      lwire = (if owner'p then freeze else id) $ entry {w'val = sigma}
      gate = g {g'lwire = lwire, g'rwire = other}
  pure
    . update'rho (recip delta) gate gmap
    . update'shifter owner'p tampered'p entry'val delta epsilon gate gmap
    $ omap <<< gate
{-# INLINEABLE sign'gate #-}

-- | Local update of the involved amplifier gate by normalizing it
update'rho
  :: (Field r, Integral r, Integral q, Field q)
  => r
  -> Gate (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Omap (NIL i r q)
update'rho rho g gmap omap =
  let amp@Gate {..} = next'amp gmap g
      (NIL c _) = w'val g'rwire
      rwire = g'rwire {w'val = w'val g'rwire * nil c rho}
   in omap <<< amp {g'rwire = rwire}
{-# INLINE update'rho #-}

update'shifter
  :: (Integral r, Field r, Integral q, Field q)
  => Bool -- Is the signer's own entry?
  -> Bool -- Is the entry tampered?
  -> NIL i r q -- previous entry value
  -> r -- delta
  -> r -- epsilon
  -> Gate (NIL i r q) -- gate starts from
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Omap (NIL i r q)
update'shifter owner'p tampered'p entry'val delta epsilon g gmap omap =
  let sh@Gate {g'rwire = shifter} = get'shifter omap gmap g
      shifter'val@(NIL c _) = w'val shifter
      rval
        | tampered'p =
            if owner'p
              then
                let net'val = entry'val + shifter'val
                    sigma = w'val (g'lwire g)
                 in shifter'val * sigma + (entry'val * nil c (-delta * epsilon))
              else (shifter'val * nil c delta) + nil c (-delta * epsilon)
        | otherwise = nil c $ -delta * epsilon
      rwire = (if owner'p then freeze else id) $ shifter {w'val = rval}
   in omap <<< sh {g'rwire = rwire}
{-# INLINE update'shifter #-}

-- | Find next amplifier gate directly involved with the given gate
next'amp :: Gmap a -> Gate a -> Gate a
next'amp gmap g@Gate {g'owire = Wire {w'key = out}, ..}
  | amp'wirep g'rwire = g
  | otherwise =
      if member out gmap
        then next'amp gmap (head $ gmap ~>> out)
        else die $ "Error, not found any amp gate following: " ++ out
{-# INLINE next'amp #-}

-- | Find all previous amplifier gates directly involved with the given gate
prev'amps :: Eq a => Omap a -> Gate a -> [Gate a]
prev'amps omap g = nub $ find (g'lwire g) ++ find (g'rwire g)
 where
  find wire@Wire {..}
    | member w'key omap =
        let (gate@Gate {..}, _) = omap ~> w'key
         in if amp'wirep g'rwire then [gate] else prev'amps omap gate
    | otherwise = []
{-# INLINE prev'amps #-}

-- | Find the shifter gate involved in a given entry gate
get'shifter :: Eq a => Omap a -> Gmap a -> Gate a -> Gate a
get'shifter omap gmap g@Gate {..} =
  case g'op of
    Add
      | shift'wirep g'rwire -> g
      | otherwise -> die $ "Error, no shifter: " ++ w'key g'lwire
    Mul ->
      let unshifter = head $ gmap ~>> w'key g'owire
          (shifter'out, _) = either'by (/= g'owire) unshifter
       in fst $ omap ~> w'key shifter'out
    a -> die $ "Error, found unexpected gate op: " ++ show a
{-# INLINEABLE get'shifter #-}

-- | Check if the given amp is one of principal amps
prin'amp'p :: Omap a -> Gate a -> Bool
prin'amp'p omap g
  | xor' amp'wirep g = find (g'lwire g)
  | otherwise = die $ "Error, not amplifier wire" ++ w'key (g'rwire g)
 where
  find wire@Wire {..}
    | member w'key omap =
        let (Gate {..}, _) = omap ~> w'key
         in not (amp'wirep g'rwire) && (find g'lwire && find g'rwire)
    | otherwise = True
{-# INLINE prin'amp'p #-}

-- | Get a hash value from a given circuit
hash'gates :: ByteString -> [Gate a] -> ByteString
hash'gates salt gates =
  let from'str = sha256 . bytes'from'str
      from'ba = foldl1 ((sha256 .) . append)
      hash'wire wire = from'str (w'key wire) `append` salt
      hash'gate Gate {..} =
        case g'op of
          Add -> from'ba $ hash'wire <$> [g'lwire, g'rwire, g'owire]
          Mul -> from'ba $ hash'wire <$> [g'rwire, g'owire, g'lwire]
          _ -> from'ba $ hash'wire <$> [g'owire, g'lwire, g'rwire]
   in from'ba $ hash'gate <$> gates
{-# INLINE hash'gates #-}
