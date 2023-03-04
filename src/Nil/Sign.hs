{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Data.List (foldl', nub, sortOn)
import Data.Map (Map, assocs, elems, member)
import GHC.Generics (Generic)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, p'curve, toA, (~*))
import Nil.Data (NIL (NIL), lift, nil, unil)
import Nil.Eval (extend'gate, extend'wire, (~~))
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

-- | Aggregable-signature object for nil'sign
data Nilsig i r q p = Nilsig
  { n'hash :: String
  , n'key :: Nilkey i q p
  , n'circuit :: Circuit (NIL i r q)
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

-- | Replace previous gate with the new evaluated one
(<<<) :: Eq a => Omap a -> Gate a -> Omap a
(<<<) omap gate@Gate {g'owire = Wire {w'key}}
  | member w'key omap = omap <~ (w'key, (gate, snd $ omap ~> w'key))
  | otherwise = die $ "Error, not found gate of outwire: " ++ w'key
{-# INLINE (<<<) #-}

-- | Get the latest info of a given gate
(>>>) :: Omap a -> Gate a -> Gate a
(>>>) omap gate@Gate {g'owire = Wire {w'key}}
  | member w'key omap = fst $ omap ~> w'key
  | otherwise = die $ "Error, not found gate of outwire: " ++ w'key
{-# INLINE (>>>) #-}

-- | Initialize nil-signature
nil'init
  :: ( Integral q
     , Field q
     , Field p
     , Integral r
     , Random r
     , Bounded r
     , Field r
     )
  => Curve i q
  -> Curve i p
  -> Circuit r
  -> IO (Nilsig i r q p)
nil'init curve'q curve'p circuit = do
  phi <- ranf
  chi <- ranf
  nilified <- nilify'circuit <=< reorg'circuit $ circuit
  let omap = omap'from'gates . (extend'gate curve'q <$>) . c'gates $ nilified
      amps = find'amps omap
      key = update'nilkey phi chi (c'g curve'q, c'g curve'p)

  -- forced initial backpropagation
  (gate'map, nilkey) <- foldM (backprop 1 phi) (omap, key) amps
  pure $ Nilsig mempty nilkey (nilified {c'gates = sort'omap gate'map})
{-# INLINE nil'init #-}

update'nilkey
  :: (Integral r, Field p, Field q)
  => r
  -> r
  -> Nilkey i q p
  -> Nilkey i q p
update'nilkey a b = bimap (~* a) (~* b)
{-# INLINE update'nilkey #-}

-- | Sort Omap by height
sort'omap :: Omap a -> [Gate a]
sort'omap = (fst <$>) . sortOn snd . elems
{-# INLINE sort'omap #-}

{- | Nilsign: homomorphically ecrypt secrets based on a reorged circuit.
 Here, @sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets.
-}
nil'sign
  :: ( Field q
     , Bounded q
     , Random q
     , Integral q
     , Integral r
     , Random r
     , Bounded r
     , Field r
     , Field p
     )
  => Wmap (NIL i r q)
  -> Nilsig i r q p
  -> IO (Nilsig i r q p)
nil'sign secrets sig@Nilsig {..} = do
  alpha <- ranf
  gamma <- ranf
  let omap = omap'from'gates . c'gates $ n'circuit
      gmap = gmap'from'omap omap
      entries = find'entries omap
      amps = find'amps omap

  -- sign each entry gate with signer's own secret
  signed <- foldM (sign'gate secrets gmap) omap entries

  -- randomize all amplifier gates (obfuscation)
  (gate'map, nilkey) <- foldM (backprop alpha gamma) (signed, n'key) amps
  pure $
    sig
      { n'key = nilkey
      , n'hash
      , n'circuit = n'circuit {c'gates = sort'omap gate'map}
      }
{-# INLINE nil'sign #-}

gmap'from'omap :: Eq a => Omap a -> Gmap a
gmap'from'omap omap = foldl' update mempty gates
 where
  gates = fst <$> sortOn (negate . snd) (elems omap)
  go'wire gate gmap wire
    | out'wirep wire = gmap <<~ (w'key wire, gate)
    | otherwise = gmap
  update gmap gate@Gate {..} =
    foldl' (go'wire gate) gmap [g'lwire, g'rwire]
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

-- | Randomize the end amp and backpropagate to the other amps
backprop
  :: (Integral q, Field q, Random r, Bounded r, Integral r, Field r, Field p)
  => r
  -> r
  -> (Omap (NIL i r q), Nilkey i q p)
  -> Gate (NIL i r q)
  -> IO (Omap (NIL i r q), Nilkey i q p)
backprop alpha gamma (omap, nilkey) g = do
  beta <- ranf
  let amps = prev'amps omap g
      update rand (m, k) gate =
        let gate'@Gate {..} = m >>> gate
            val = w'val g'rwire * nil (p'curve . fst $ k) rand
            rwire = g'rwire {w'val = val}
         in (m <<< gate' {g'rwire = rwire}, nilkey)
      acc
        | final'amp'p omap g = (omap, update'nilkey 1 (recip alpha) nilkey)
        | prin'amp'p omap g =
            ( fst $ update gamma (omap, nilkey) g
            , update'nilkey gamma (recip gamma) nilkey
            )
        | otherwise = update beta (omap, nilkey) g
  pure $ foldl' (update (recip beta)) acc amps
{-# INLINE backprop #-}

-- | Sign each entry gate assigned for a signer
sign'gate
  :: (Random r, Bounded r, Integral r, Integral q, Field r, Field q)
  => Wmap (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> IO (Omap (NIL i r q))
sign'gate secrets gmap omap g = do
  delta <- ranf
  epsilon <- ranf
  let (entry, other) = either'by entry'wirep g
  if member (w'key entry) secrets
    then do
      let multiplier = recip delta
          unshifter = -delta * epsilon
          shifted = delta * unil (w'val (secrets ~> w'key entry)) + epsilon
       in pure
            . nilify False False (next'amp gmap g) multiplier
            . nilify False True (get'shifter omap gmap g) unshifter
            . nilify True True g shifted
            $ omap
    else pure omap
{-# INLINEABLE sign'gate #-}

-- | Tamper the unlifted value of gates and mix them with random numbers
nilify
  :: (Integral r, Integral q, Field r, Field q)
  => Bool -- which side to update? lwire -> True, rwire: False
  -> Bool -- the wire to be frozen?
  -> Gate (NIL i r q)
  -> r
  -> Omap (NIL i r q)
  -> Omap (NIL i r q)
nilify right fin g val omap =
  let gate@Gate {g'lwire = gl, g'rwire = gr} = omap >>> g
      NIL c _ = w'val gl
      finish = if fin then freeze else id
      gate' =
        if right
          then gate {g'lwire = finish $ gl {w'val = w'val gl * nil c val}}
          else gate {g'rwire = finish $ gr {w'val = w'val gr * nil c val}}
   in omap <<< gate'
{-# INLINE nilify #-}

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
{-# INLINE get'shifter #-}

final'amp'p :: Omap a -> Gate a -> Bool
final'amp'p omap g =
  let (Gate {g'rwire = Wire {w'key = amp'key}}, _) = omap ~> end'key
   in w'key (g'owire g) == amp'key
{-# INLINE final'amp'p #-}

-- | Check if the given amp is one of principal amps
prin'amp'p :: Omap a -> Gate a -> Bool
prin'amp'p omap g
  | xor' amp'wirep g = find (g'lwire g)
  | otherwise = die $ "Error, not amplifier wire: " ++ w'key (g'rwire g)
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

-- | Eval nil-signature
nil'eval :: Nilsig i r q p -> Wmap (NIL i r q) -> Wire (NIL i r q)
nil'eval Nilsig {..} pubs = undefined
