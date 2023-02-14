{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

-----------------------------------------------------------------------------
-- nilsign: partially evaluate circuit with secrets
--------------------------------------------------------------------------------

module Nil.Sign where

import Control.DeepSeq (NFData)
import Control.Monad (foldM)
import Data.List (foldl', nub, sortOn)
import Data.Map (Map, assocs, elems, member)
import Nil.Circuit
import Nil.Curve (Curve, Point (..), (.*))
import Nil.Ecdata (G1, G2)
import Nil.Eval (p'from'wire, wire'from'p)
import Nil.Field (Field)
import Nil.Reorg
  ( O'table
  , amp'wirep
  , otab'from'gates
  , reorg'circuit
  , shift'wirep
  )
import Nil.Utils (Pretty, die, ranf)
import System.Random (Random)

-- | Multiple-signature object for nil-sign
data NilSig f = NilSig
  { n'nilkey :: NilKey
  , n'hash :: String
  , n'sig :: Circuit f
  }
  deriving (Eq, Show)

-- | Pretty printer for NilSig f
instance Show f => Pretty (NilSig f)

type NilKey = (Point G1, Point G2)

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
hide curve wire =
  set'key (w'key wire)
    . set'expr frozen'expr
    . wire'from'p
    . p'from'wire curve
    $ wire

-- | Shift a value of wire over field using crypto-safe random variables
shift'wire :: Num f => f -> f -> Wire f -> Wire f
shift'wire delta epsilon wire@Wire {..} =
  set'expr frozen'expr
    . set'val (delta * (w'val + epsilon))
    $ wire

-- | Initialize nil-signature
init'sig :: (Eq f, Num f, Show f) => Circuit f -> IO (NilSig f)
init'sig circuit = NilSig (O, O) mempty <$> reorg'circuit circuit
{-# INLINE init'sig #-}

{- | Nilsign: homomorphically ecrypt secrets based on a reorged circuit.
 Here, @sign@ means doing repeatdly evaluate a reorged-circuit with the given secrets.
-}
nilsign
  :: ( Eq f
     , Fractional f
     , Random f
     , Field f
     , Bounded f
     , Integral k
     , Field k
     , Integral f
     , Fractional k
     , NFData k
     )
  => Curve k
  -> NilSig f
  -> W'table f
  -> IO (NilSig f)
nilsign curve nilsig@NilSig {..} secrets = do
  phi <- ranf
  chi <- ranf
  let o'tab = otab'from'gates . c'gates $ n'sig
      g'tab = gtab'from'otab o'tab
  signed <-
    foldM
      (sign'gate curve secrets g'tab)
      o'tab
      (find'entries o'tab)
  let gates =
        (fst <$>) . sortOn snd . elems $
          foldl'
            (update'kappa phi chi)
            signed
            (fst . (signed ~>) <$> get'amp'keys signed)
  pure $
    nilsig
      { n'nilkey = update'nilkey phi chi n'nilkey
      , n'hash
      , n'sig = n'sig {c'gates = gates}
      }
{-# INLINE nilsign #-}

find'entries :: O'table f -> [Gate f]
find'entries table =
  [ g | (g, _) <- elems table, g'op g /= End, xor' entry'wirep g
  ]
{-# INLINE find'entries #-}

{- | Update kappa value in amplifier gates:
 Kappa := Pi_j (phi + chi) * (phi - chi)
-}
update'kappa :: (Eq f, Num f) => f -> f -> O'table f -> Gate f -> O'table f
update'kappa phi chi o'tab g@Gate {..} =
  o'tab
    <<< ( w'key g'owire
        , g
            { g'rwire =
                g'rwire
                  { w'val = w'val g'rwire * (phi + chi) * (phi - chi)
                  }
            }
        )
{-# INLINE update'kappa #-}

-- | Update nilkey (verification key) -> (PHI, CHI)
update'nilkey :: Integral f => f -> f -> NilKey -> NilKey
update'nilkey phi chi (_PHI, _CHI) = (_PHI .* (phi + chi), _CHI .* (phi - chi))
{-# INLINE update'nilkey #-}

sign'gate
  :: ( Eq f
     , Fractional f
     , Field f
     , Random f
     , Bounded f
     , Integral f
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
      secret = secrets ~~> entry
      shift' = shift'wire delta epsilon
      hide' = hide curve . shift'
  case g'op of
    Add -> do
      let gate =
            g
              { g'lwire = hide' secret
              , g'rwire = if shift'wirep other then hide' unit'const else other
              }
      pure
        . update'amp (recip delta) (find'amp g'tab g)
        $ o'tab <<< (w'key g'owire, gate)
    Mul -> do
      let gate =
            g
              { g'lwire = shift' secret
              , g'rwire = other
              }
      pure
        . update'amp (recip delta) (find'amp g'tab g)
        $ o'tab <<< (w'key g'owire, gate)
    a -> die $ "Error, found unexpected gate op: " ++ show a

-- update'shift delta epsilon (find'shift o'tab g'tab g)
-- lwire = shift'wire delta epsilon secret
-- rwire = case g'op of
-- Add ->
-- if shift'wirep other
-- then hide curve . shift'wire delta epsilon $ unit'const
-- else other
-- Mul -> other
-- a -> die $ "Error, found unexpected gate op: " ++ show a
-- update'gate =
-- o'tab
-- <<< (w'key g'owire, g {g'lwire = lwire, g'rwire = rwire})
-- pure
-- . update'amp (recip delta) (find'amp g'tab g)
-- . update'shift delta epsilon (find'shift o'tab g'tab g)
-- \$ update'gate
{-# INLINEABLE sign'gate #-}

update'shift
  :: (Eq f, Num f) => f -> f -> Gate f -> O'table f -> O'table f
update'shift delta epsilon g@Gate {..} o'tab =
  if
      | g'op == Add && not (shift'wirep g'rwire) -> undefined
      | g'op == Mul ->
          let rwire =
                g'rwire {w'val = negate $ w'val g'rwire * delta * epsilon}
           in o'tab <<< (w'key g'owire, g {g'rwire = rwire})
      | otherwise -> o'tab

update'amp
  :: (Eq f, Num f) => f -> Gate f -> O'table f -> O'table f
update'amp rho g@Gate {..} o'tab =
  o'tab
    <<< ( w'key g'owire
        , g
            { g'rwire =
                g'rwire {w'val = w'val g'rwire * rho}
            }
        )
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

-- | Find the amplifier-knot gate related to the given gate
find'amp :: G'table f -> Gate f -> Gate f
find'amp table g@Gate {..}
  | amp'wirep g'rwire = g
  | otherwise = find'amp table (head $ table ~>> w'key g'owire)
{-# INLINEABLE find'amp #-}

-- | Find the shift-knot gate related to the given gate
find'shift :: Eq f => O'table f -> G'table f -> Gate f -> Gate f
find'shift o'tab g'tab g@Gate {..}
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
{-# INLINEABLE find'shift #-}

-- | Get a list of keys of amplifier gates
get'amp'keys :: O'table f -> [String]
get'amp'keys table = foldl' get [] (assocs table)
 where
  get keys (key, (gate, _))
    | xor' amp'wirep gate = key : keys
    | otherwise = keys
{-# INLINE get'amp'keys #-}

entry'wirep :: Wire f -> Bool
entry'wirep wire =
  and $
    [ not . out'wirep
    , not . shift'wirep
    , not . amp'wirep
    , not . frozen'wirep
    ]
      <*> [wire]
{-# INLINE entry'wirep #-}

frozen'expr :: String
frozen'expr = "__FROZEN__"

frozen'wirep :: Wire f -> Bool
frozen'wirep Wire {..} = w'expr == frozen'expr

freeze :: Wire f -> Wire f
freeze = set'expr frozen'expr
