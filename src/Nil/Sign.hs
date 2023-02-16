{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

-----------------------------------------------------------------------------
-- nilsign: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

module Nil.Sign where

import Control.DeepSeq (NFData)
import Control.Monad (foldM)
import Data.ByteString (append)
import Data.List (foldl', nub, sortOn)
import Data.Map (Map, assocs, elems, member)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), c'g, toA, (.*))
import Nil.Ecdata (G1, G2)
import Nil.Eval (p'from'wire, wire'from'p)
import Nil.Field (Field)
import Nil.Reorg
  ( O'table
  , amp'wirep
  , entry'wirep
  , freeze
  , otab'from'gates
  , reorg'circuit
  , shift'wirep
  )
import Nil.Utils (Pretty (..), bytes'from'str, die, hex'from'bytes, ranf, sha256, tmap)
import System.Random (Random)

-- | Multiple-signature object for nil-sign
data NilSig f k q = NilSig
  { nil'hash :: String
  , nil'key :: NilKey k q
  , nil'circuit :: Circuit f
  }
  deriving (Eq, Show)

instance (Show f, Show k, Show q) => Pretty (NilSig f k q)

-- | Aggregable verification key of nilsig
type NilKey k q = (Point k, Point q)

instance (Show k, Pretty k, Show q, Pretty q) => Pretty (NilKey k q) where
  pretty key = unlines [pretty . fst $ key, pretty . snd $ key]

-- | Lookup table describing a circuit as DAG
type G'table f = Map String [Gate f]

{- | Put an edge record to the graph-table
 key -> out-wire of [FROM gate]
 gate -> [TO gate]
-}
(<<~) :: Eq f => G'table f -> (String, Gate f) -> G'table f
(<<~) table (key, gate)
  | member key table =
      let gates = table ~> key
       in table <~ (key, nub $ gate : gates)
  | otherwise = table <~ (key, [gate])
{-# INLINE (<<~) #-}

-- | Follow a wire to traverse graph
(~>>) :: G'table f -> String -> [Gate f]
(~>>) table key
  | member key table = table ~> key
  | otherwise = die $ "Error, reached a deadend wire: " ++ key

-- | Overwrite/replace previous gate with the new evaluated one
(<<<) :: Eq f => O'table f -> (String, Gate f) -> O'table f
(<<<) table (key, gate)
  | member key table =
      let (_, height) = table ~> key
       in table <~ (key, (gate, height))
  | otherwise = die $ "Error, not found gate-key: " ++ key
{-# INLINE (<<<) #-}

-- | Homomorphically hide using a base point of the given elliptic curve
hide
  :: (Integral f, Fractional f, Integral k, Field k, Fractional k, NFData k)
  => Curve k
  -> Wire f
  -> Wire f
hide curve =
  freeze
    . wire'from'p
    . p'from'wire curve

-- | Shift a value of wire over field using crypto-safe random variables
shift'wire :: Num f => f -> f -> Wire f -> Wire f
shift'wire delta epsilon wire@Wire {..} =
  freeze
    . set'val (delta * (w'val + epsilon))
    $ wire

-- | Eval nil-signature
eval'nilsig :: NilSig f k q -> W'table f -> Wire f
eval'nilsig NilSig {..} pubs =
  foldl' go pubs (c'gates nil'circuit) ~> "return"
 where
  go table g@Gate {..} =
    case g'op of
      Add -> undefined
      Mul -> undefined
      a -> die "Error,"

-- | Initialize nil-signature
init'nilsig
  :: ( Eq f
     , Num f
     , Show f
     , Eq k
     , Fractional k
     , Field k
     , Eq q
     , Fractional q
     , Field q
     )
  => Curve k
  -> Curve q
  -> Circuit f
  -> IO (NilSig f k q)
init'nilsig k q circuit =
  NilSig mempty (c'g k, c'g q) <$> reorg'circuit circuit
{-# INLINE init'nilsig #-}

{- | Nilsign: homomorphically ecrypt secrets based on a reorged circuit.
 Here, @sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets.
-}
nilsign
  :: ( Eq f
     , Integral f
     , Fractional f
     , Random f
     , Field f
     , Bounded f
     , Integral k
     , Fractional k
     , Field k
     , NFData k
     , Eq q
     , Fractional q
     , Field q
     , NFData q
     )
  => Curve k
  -> Curve q
  -> NilSig f k q
  -> W'table f
  -> IO (NilSig f k q)
nilsign
  curve'k
  curve'q
  nilsig@NilSig {nil'key = (point'k, point'q), ..}
  secrets = do
    phi <- ranf
    chi <- ranf
    let o'tab = otab'from'gates . c'gates $ nil'circuit
        g'tab = gtab'from'otab o'tab
        entries = find'entries o'tab
    signed <- foldM (sign'gate curve'k secrets g'tab) o'tab entries
    let amps = find'amps signed
        final = foldl' (freeze'amp phi chi) signed amps
    pure $
      nilsig
        { nil'key =
            ( toA $ point'k .* (phi + chi)
            , toA $ point'q .* (phi - chi)
            )
        , nil'hash
        , nil'circuit =
            nil'circuit {c'gates = (fst <$>) . sortOn snd $ elems final}
        }
{-# INLINE nilsign #-}

-- | Find a list of entry gates
find'entries :: O'table f -> [Gate f]
find'entries table =
  [ g | (g, _) <- elems table, g'op g /= End, xor' entry'wirep g
  ]
{-# INLINE find'entries #-}

-- | Find a list of amplifier gates
find'amps :: O'table f -> [Gate f]
find'amps table = foldl' go [] (assocs table)
 where
  go gates (_, (gate, _))
    | xor' amp'wirep gate = gate : gates
    | otherwise = gates
{-# INLINE find'amps #-}

{- | Update kappa value in each amplifier gates and finalize amplifiers
 Kappa := Pi_j (phi + chi) * (phi - chi)
-}
freeze'amp :: (Eq f, Num f) => f -> f -> O'table f -> Gate f -> O'table f
freeze'amp phi chi o'tab g@Gate {..} =
  let rwire =
        g'rwire
          { w'val = w'val g'rwire * (phi + chi) * (phi - chi)
          }
   in o'tab <<< (w'key g'owire, g {g'rwire = rwire})
{-# INLINE freeze'amp #-}

sign'gate
  :: ( Eq f
     , Integral f
     , Fractional f
     , Field f
     , Random f
     , Bounded f
     , Integral k
     , Fractional k
     , Field k
     , NFData k
     )
  => Curve k
  -> W'table f
  -> G'table f
  -> O'table f
  -> Gate f
  -> IO (O'table f)
sign'gate curve secrets g'tab o'tab g@Gate {..} = do
  delta <- ranf
  epsilon <- ranf
  let (entry, other) = either'by entry'wirep g
  if not (member (w'key entry) secrets) && not (const'wirep entry)
    then pure o'tab -- do not sign secret variables for others
    else do
      let secret = secrets ~~> entry
          randomize = shift'wire delta epsilon
          lift = hide curve . randomize
          gate = case g'op of
            Add ->
              let rwire = if shift'wirep other then lift unit'const else other
               in g {g'lwire = lift secret, g'rwire = rwire}
            Mul -> g {g'lwire = randomize secret, g'rwire = other}
            a -> die $ "Error, found unexpected gate op: " ++ show a
      pure
        . update'amp delta g g'tab
        . update'shift curve delta epsilon g g'tab
        $ o'tab <<< (w'key g'owire, gate)
{-# INLINEABLE sign'gate #-}

update'shift
  :: ( Eq f
     , Num f
     , Integral f
     , Fractional f
     , Integral k
     , Fractional k
     , Field k
     , NFData k
     )
  => Curve k
  -> f
  -> f
  -> Gate f
  -> G'table f
  -> O'table f
  -> O'table f
update'shift curve delta epsilon g g'tab o'tab
  | shift'wirep . g'rwire $ g = o'tab
  | otherwise =
      let shift@Gate {..} = get'shift o'tab g'tab g
          rwire = g'rwire {w'val = negate $ w'val g'rwire * delta * epsilon}
          updater
            | g'op == Add = hide curve
            | otherwise = freeze
       in o'tab <<< (w'key g'owire, shift {g'rwire = updater rwire})
{-# INLINE update'shift #-}

update'amp
  :: (Eq f, Num f, Fractional f)
  => f
  -> Gate f
  -> G'table f
  -> O'table f
  -> O'table f
update'amp delta g g'tab o'tab =
  let amp@Gate {..} = get'amp g'tab g
      rwire = g'rwire {w'val = w'val g'rwire * recip delta}
   in o'tab <<< (w'key g'owire, amp {g'rwire = rwire})
{-# INLINE update'amp #-}

gtab'from'otab :: Eq f => O'table f -> G'table f
gtab'from'otab o'tab =
  let gates = fst <$> sortOn (negate . snd) (elems o'tab)
      go'wire gate g'tab wire
        | out'wirep wire = g'tab <<~ (w'key wire, gate)
        | otherwise = g'tab
      update g'tab gate@Gate {..} =
        foldl' (go'wire gate) g'tab [g'lwire, g'rwire]
   in foldl' update mempty gates
{-# INLINEABLE gtab'from'otab #-}

-- | Find the amplifier gate related to the given gate
get'amp :: G'table f -> Gate f -> Gate f
get'amp table g@Gate {..}
  | amp'wirep g'rwire = g
  | otherwise = get'amp table (head $ table ~>> w'key g'owire)
{-# INLINEABLE get'amp #-}

-- | Find the shift gate related to the given gate
get'shift :: Eq f => O'table f -> G'table f -> Gate f -> Gate f
get'shift o'tab g'tab g@Gate {..}
  | xor' entry'wirep g =
      case g'op of
        Add
          | shift'wirep g'rwire -> g
          | otherwise ->
              let (ext, _) = either'by out'wirep g
               in fst $ o'tab ~> w'key ext
        Mul ->
          let next = head $ g'tab ~>> w'key g'owire
              (wire, _) = either'by (/= g'owire) next
           in fst $ o'tab ~> w'key wire
        a -> die $ "Error, found unexpected gate op: " ++ show a
  | otherwise = die $ "Error, not a shifted gate of: " ++ w'key g'owire
{-# INLINEABLE get'shift #-}

-- | Get a hash value from a given circuit
hash'circuit :: String -> Circuit f -> String
hash'circuit salt Circuit {..} =
  let from'str = sha256 . bytes'from'str
      from'ba = foldl1 ((sha256 .) . append)
      hash'wire Wire {..} = from'str (w'key ++ salt)
      hash'gate Gate {..} =
        case g'op of
          Add -> from'ba $ hash'wire <$> [g'lwire, g'rwire, g'owire]
          Mul -> from'ba $ hash'wire <$> [g'rwire, g'lwire, g'owire]
          _ -> from'ba $ hash'wire <$> [g'owire, g'lwire, g'rwire]
   in hex'from'bytes . from'ba $ hash'gate <$> c'gates
{-# INLINE hash'circuit #-}
