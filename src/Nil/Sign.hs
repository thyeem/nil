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
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, p'curve, toA, (~*))
import Nil.Data (NIL (NIL), lift, nil)
import Nil.Eval (extend'gate, extend'wire)
import Nil.Field (Field)
import Nil.Reorg
  ( Omap
  , amp'wirep
  , and'
  , either'by
  , entry'wirep
  , freeze
  , nilify'circuit
  , nor'
  , omap'from'gates
  , reorg'circuit
  , shift'wirep
  , xor'
  )
import Nil.Utils (Pretty (..), bytes'from'str, die, ranf, sha256, tmap)
import System.Random (Random)

-- | Aggregable-signature object for nilsign
data Nilsig i r q p = Nilsig
  { nil'hash :: String
  , nil'key :: Nilkey i q p
  , nil'circuit :: Circuit (NIL i r q)
  }
  deriving (Eq, Show)

instance (Show q, Field q, Show p, Field p, Show r) => Pretty (Nilsig i r q p)

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
(<<~) map (key, gate)
  | member key map =
      let gates = map ~> key
       in map <~ (key, nub $ gate : gates)
  | otherwise = map <~ (key, [gate])
{-# INLINE (<<~) #-}

-- | Follow a wire to traverse graph
(~>>) :: Gmap a -> String -> [Gate a]
(~>>) map key
  | member key map = map ~> key
  | otherwise = die $ "Error, reached a deadend wire: " ++ key

-- | Overwrite/replace previous gate with the new evaluated one
(<<<) :: Eq a => Omap a -> (String, Gate a) -> Omap a
(<<<) map (key, gate)
  | member key map =
      let (_, height) = map ~> key
       in map <~ (key, (gate, height))
  | otherwise = die $ "Error, not found gate-key: " ++ key
{-# INLINE (<<<) #-}

-- | Eval nil-signature
verify'sig :: Nilsig i r q p -> Wmap (NIL i r q) -> Wire (NIL i r q)
verify'sig Nilsig {..} pubs = undefined

-- | Initialize nil-signature
init'sig
  :: (Field q, Field p, Eq r, Num r, Show r)
  => Curve i q
  -> Curve i p
  -> Circuit r
  -> IO (Nilsig i r q p)
init'sig curve'q curve'p circuit = do
  nilified@Circuit {..} <- nilify'circuit <=< reorg'circuit $ circuit
  pure $
    Nilsig
      mempty
      (c'g curve'q, c'g curve'p)
      (nilified {c'gates = extend'gate curve'q <$> c'gates})
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
    phi <- ranf
    chi <- ranf
    let c = p'curve phi'p
        x'secrets = extend'wire c <$> secrets
        omap = omap'from'gates . c'gates $ nil'circuit
        gmap = gmap'from'omap omap
        entries = find'entries omap
    signed <- foldM (sign'gate x'secrets gmap) omap entries
    let amps = find'amps signed
        done = foldl' (update'kappa phi chi) signed amps
    pure $
      sig
        { nil'key =
            ( toA $ phi'p ~* (phi + chi)
            , toA $ chi'p ~* (phi - chi)
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
find'entries map =
  [g | (g, _) <- elems map, g'op g /= End, xor' entry'wirep g]
{-# INLINE find'entries #-}

-- | Find a list of amplifier gates
find'amps :: Omap a -> [Gate a]
find'amps map = foldl' go [] (assocs map)
 where
  go gates (_, (gate, _))
    | xor' amp'wirep gate = gate : gates
    | otherwise = gates
{-# INLINE find'amps #-}

{- | Update kappa value in each amplifier gates and finalize amplifiers
 Kappa := Pi_j (phi + chi) * (phi - chi)
-}
update'kappa
  :: (Eq r, Num r, Eq q, Integral r, Integral q, Field r, Field q)
  => r
  -> r
  -> Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> Omap (NIL i r q)
update'kappa phi chi omap g@Gate {..} =
  let (NIL c _) = w'val g'rwire
      val = w'val g'rwire * nil c (phi + chi) * nil c (phi - chi)
      rwire = g'rwire {w'val = val}
   in omap <<< (w'key g'owire, g {g'rwire = rwire})
{-# INLINE update'kappa #-}

-- | Sign each entry gate assigned for a signer
sign'gate
  :: Wmap (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Gate (NIL i r q)
  -> IO (Omap a)
sign'gate secrets gmap omap g@Gate {..} = undefined
-- delta <- pure 1 -- ranf
-- epsilon <- pure 2 -- ranf
-- let (entry, other) = either'by entry'wirep g
-- if not (member (w'key entry) secrets) && not (const'wirep entry)
-- then pure omap -- do not sign secret variables for others
-- else do
-- let secret = secrets ~~> entry
-- randomize = shift'wire delta epsilon
-- lift = hide curve . randomize
-- gate = case g'op of
-- Add ->
-- let rwire
-- \| shift'wirep other =
-- lift $ val'const (negate $ delta * epsilon)
-- \| otherwise = other
-- in g {g'lwire = lift secret, g'rwire = rwire}
-- Mul -> g {g'lwire = randomize secret, g'rwire = other}
-- a -> die $ "Error, found unexpected gate op: " ++ show a
-- pure
-- . update'rho delta g gmap
-- . update'shift curve delta epsilon g gmap
-- \$ omap <<< (w'key g'owire, gate)
{-# INLINEABLE sign'gate #-}

update'rho
  :: (Field r, Integral r, Integral q, Field q)
  => r
  -> Gate (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Omap (NIL i r q)
update'rho delta g gmap omap =
  let amp@Gate {..} = get'amp gmap g
      (NIL c _) = w'val g'rwire
      rwire = g'rwire {w'val = w'val g'rwire * nil c (recip delta)}
   in omap <<< (w'key g'owire, amp {g'rwire = rwire})
{-# INLINE update'rho #-}

update'shift
  :: (Field q, Integral r, Integral q)
  => r
  -> r
  -> Gate (NIL i r q)
  -> Gmap (NIL i r q)
  -> Omap (NIL i r q)
  -> Omap (NIL i r q)
update'shift delta epsilon g gmap omap
  | shift'wirep . g'rwire $ g = omap
  | otherwise =
      let g@Gate {..} = get'shift omap gmap g
          (NIL c _) = w'val g'rwire
          val =
            (if g'op == Add then lift else id)
              . nil c
              . negate
              $ delta * epsilon
          rwire = freeze g'rwire {w'val = val}
       in omap <<< (w'key g'owire, g {g'rwire = rwire})
{-# INLINE update'shift #-}

-- | Find the amplifier gate related to the given gate
get'amp :: Gmap a -> Gate a -> Gate a
get'amp map g@Gate {..}
  | amp'wirep g'rwire = g
  | otherwise = get'amp map (head $ map ~>> w'key g'owire)
{-# INLINEABLE get'amp #-}

-- | Find the shift gate related to the given gate
get'shift :: Eq a => Omap a -> Gmap a -> Gate a -> Gate a
get'shift omap gmap g@Gate {..}
  | xor' entry'wirep g =
      case g'op of
        Add
          | shift'wirep g'rwire -> g
          | otherwise ->
              let (ext, _) = either'by out'wirep g
               in fst $ omap ~> w'key ext
        Mul ->
          let next = head $ gmap ~>> w'key g'owire
              (wire, _) = either'by (/= g'owire) next
           in fst $ omap ~> w'key wire
        a -> die $ "Error, found unexpected gate op: " ++ show a
  | otherwise = die $ "Error, not a shifted gate of: " ++ w'key g'owire
{-# INLINEABLE get'shift #-}

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
