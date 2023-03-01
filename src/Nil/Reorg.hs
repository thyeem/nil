{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Nil.Reorg where

import Control.Applicative (liftA2)
import Data.Bifunctor (bimap)
import Data.List (foldl', nub)
import Data.Map (Map, insert, member)
import Nil.Circuit
import Nil.Utils (die, random'hex)

-- | Map describing a circuit with height from entry nodes
type Omap a = Map String (Gate a, Int)

(+++) :: Applicative f => f [a] -> f [a] -> f [a]
(+++) = liftA2 (++)
{-# INLINE (+++) #-}

-- | Test logical operator (AND) with a predicate and input wires
and' :: (Wire a -> Bool) -> Gate a -> Bool
and' p Gate {..} = p g'lwire && p g'rwire
{-# INLINE and' #-}

-- | Test logical operator (XOR) with a predicate and input wires
xor' :: (Wire a -> Bool) -> Gate a -> Bool
xor' p g = not (and' p g) && not (nor' p g)
{-# INLINE xor' #-}

-- | Test logical operator (NOR) with a predicate and input wires
nor' :: (Wire a -> Bool) -> Gate a -> Bool
nor' p Gate {..} = not $ p g'lwire || p g'rwire
{-# INLINE nor' #-}

{- | Classfy input wires satisfying the given predicate: (pass, fail)
   The result is valid only when applied input wires hold XOR
-}
either'by :: (Wire a -> Bool) -> Gate a -> (Wire a, Wire a)
either'by p g@Gate {..}
  | xor' p g = if p g'lwire then (g'lwire, g'rwire) else (g'rwire, g'lwire)
  | otherwise =
      die $
        unwords ["Error, not XOR between:", w'key g'lwire, "and", w'key g'rwire]

-- | Inspect operators
valid'operator :: Gate a -> Bool
valid'operator Gate {..} = g'op `elem` [Mul, Add, End]
{-# INLINE valid'operator #-}

-- | When merge happens
needs'merge :: Gate a -> Bool
needs'merge g@Gate {..} =
  w'recip g'rwire
    || (and' out'wirep g && g'op == Mul)
{-# INLINE needs'merge #-}

-- | Create a helper knot wire having a hashed unique key
rand'wire :: Num a => IO (Wire a)
rand'wire =
  set'expr "rand-tie"
    . unit'var
    . ("~x" ++)
    <$> random'hex 8
{-# INLINE rand'wire #-}

-- | Toggle the reciprocal flag
recip' :: Wire a -> Wire a
recip' wire@Wire {..} = wire {w'recip = not w'recip}
{-# INLINE recip' #-}

-- | Determine which wire will be cut: in forms of (survived, killed)
tip'cut :: Omap a -> String -> (Wire a, Wire a)
tip'cut omap key =
  let (Gate {g'lwire, g'rwire}, _) = omap ~> key
      height wire
        | member (w'key wire) omap = snd (omap ~> w'key wire)
        | otherwise = -1
   in if w'recip g'rwire || (height g'lwire > height g'rwire)
        then (g'lwire, g'rwire)
        else (g'rwire, g'lwire)
{-# INLINE tip'cut #-}

-- | nil-circuit
reorg'circuit :: (Eq a, Num a) => Circuit a -> IO (Circuit a)
reorg'circuit circuit@Circuit {..} = do
  let key = w'key . g'owire . last $ c'gates
      omap = omap'from'gates c'gates
  reorged <- nub <$> reorg omap key
  pure $ circuit {c'gates = reorged}
{-# INLINE reorg'circuit #-}

-- | Generate a Omap used in circuit reorg process.
omap'from'gates :: [Gate a] -> Omap a
omap'from'gates = foldl' update mempty
 where
  update omap g@Gate {..} =
    let height = max (find g'lwire) (find g'rwire)
        find Wire {w'key}
          | member w'key omap = 1 + snd (omap ~> w'key)
          | otherwise = 1
     in insert (w'key g'owire) (g, height) omap
{-# INLINE omap'from'gates #-}

-- | Reconstruct gates and wires of a given circuit for use of nilsign
reorg :: (Eq a, Num a) => Omap a -> String -> IO [Gate a]
reorg omap key
  | member key omap = do
      let (g@Gate {..}, _) = omap ~> key
          (tip, cut) = tip'cut omap key
      if
          | not . valid'operator $ g ->
              die $ "Error, found invalid op during reorg: " ++ show g'op
          | needs'merge g ->
              reorg omap (w'key tip) +++ merge omap g'owire tip cut
          | otherwise ->
              reorg omap (w'key tip) +++ reorg omap (w'key cut) +++ pure [g]
  | otherwise = pure []
{-# INLINEABLE reorg #-}

-- | merge
merge :: (Eq a, Num a) => Omap a -> Wire a -> Wire a -> Wire a -> IO [Gate a]
merge omap out tip cut
  | member (w'key cut) omap = do
      let (Gate {g'op}, _) = omap ~> w'key cut
      case g'op of
        Mul -> merge'mul omap out tip cut
        Add -> merge'add omap out tip cut
        op -> die $ "Error, unexpected operator: " ++ show op
  | otherwise = pure [Gate Mul tip cut out]
{-# INLINEABLE merge #-}

merge'mul :: (Eq a, Num a) => Omap a -> Wire a -> Wire a -> Wire a -> IO [Gate a]
merge'mul omap out tip cut = do
  let op = if w'recip cut then recip' else id
      (tip_, cut_) = bimap op op $ tip'cut omap (w'key cut)
  tie <- rand'wire
  merge omap tie tip tip_ +++ merge omap out tie cut_
{-# INLINEABLE merge'mul #-}

merge'add :: (Eq a, Num a) => Omap a -> Wire a -> Wire a -> Wire a -> IO [Gate a]
merge'add omap out tip cut = do
  if w'recip cut
    then
      die . unlines $
        [ "Error, failed to reorg the wire in circuit: " ++ w'expr cut
        , "A divisor of (/) should be a const value when it is involved with (+)"
        ]
    else do
      let (tip_, cut_) = tip'cut omap (w'key cut)
      tie'a <- rand'wire
      tie'b <- rand'wire
      merge omap tie'a tip tip_
        +++ merge omap tie'b tip cut_
        +++ pure [Gate Add tie'a tie'b out]
{-# INLINEABLE merge'add #-}

-- | The name prepared wire representing delta-shift
shift'expr :: String
shift'expr = ">>"
{-# INLINE shift'expr #-}

-- | The name prepared wire representing amplifier-knot
amp'expr :: String
amp'expr = "*/"
{-# INLINE amp'expr #-}

frozen'expr :: String
frozen'expr = "##"
{-# INLINE frozen'expr #-}

freeze :: Wire a -> Wire a
freeze = set'expr frozen'expr . set'key const'key
{-# INLINE freeze #-}

shifter :: Num a => Wire a
shifter = set'expr shift'expr unit'const
{-# INLINE shifter #-}

amplifier :: Num a => Wire a
amplifier = set'expr amp'expr unit'const
{-# INLINE amplifier #-}

-- | Predicate for a delta-shifter
shift'wirep :: Wire a -> Bool
shift'wirep Wire {..} =
  w'key == const'key
    && w'expr == shift'expr
{-# INLINE shift'wirep #-}

-- | Predicate for a amplifier-knot
amp'wirep :: Wire a -> Bool
amp'wirep Wire {..} =
  w'key == const'key
    && w'expr == amp'expr
{-# INLINE amp'wirep #-}

frozen'wirep :: Wire a -> Bool
frozen'wirep Wire {..} = w'expr == frozen'expr
{-# INLINE frozen'wirep #-}

entry'wirep :: Wire a -> Bool
entry'wirep wire =
  and $
    [ not . out'wirep
    , not . shift'wirep
    , not . amp'wirep
    , not . frozen'wirep
    ]
      <*> [wire]
{-# INLINE entry'wirep #-}

-- | nilify-circuit
nilify'circuit :: Num a => Circuit a -> IO (Circuit a)
nilify'circuit circuit@Circuit {..} = do
  shifted <- concat <$> mapM shift'gate c'gates
  let omap = omap'from'gates shifted
  nilified <- concat <$> mapM (amplify'gate omap) shifted
  pure $ circuit {c'gates = nilified}
{-# INLINE nilify'circuit #-}

-- | Add shifting gates to each entry gate
shift'gate :: Num a => Gate a -> IO [Gate a]
shift'gate g@Gate {..}
  | g'op == End = pure [g]
  | xor' out'wirep g = do
      let (ext, scalar) = either'by out'wirep g
      shift g'op scalar ext g'owire
  | nor' out'wirep g = do
      tie <- rand'wire
      pure [Gate Add g'lwire shifter tie]
        +++ shift g'op g'rwire tie g'owire
  | otherwise = pure [g]
{-# INLINEABLE shift'gate #-}

-- | Create shift gates and tie them up
shift :: Num a => Gateop -> Wire a -> Wire a -> Wire a -> IO [Gate a]
shift op scalar ext out = do
  tie'a <- rand'wire
  tie'b <- rand'wire
  case op of
    Mul ->
      pure [Gate Mul scalar ext tie'a]
        +++ pure [Gate Mul ext shifter tie'b]
        +++ pure [Gate Add tie'a tie'b out]
    Add ->
      pure [Gate Add scalar shifter tie'a]
        +++ pure [Gate Add ext tie'a out]
    _ -> die "Error,"
{-# INLINEABLE shift #-}

-- | Add an amplifier gate when needed
amplify'gate :: Num a => Omap a -> Gate a -> IO [Gate a]
amplify'gate omap g@Gate {g'lwire, g'rwire, g'owire, g'op = op}
  | op /= Add = pure [g]
  | and' from'add g = do
      (lwire, lamp) <- amplify (from'add'add g'lwire) g'lwire
      (rwire, ramp) <- amplify (from'add'add g'rwire) g'rwire
      pure lamp +++ pure ramp +++ pure [Gate Add lwire rwire g'owire]
  | otherwise = pure [g]
 where
  from'add = check ((== Add) . g'op)
  from'add'add = check (and' from'add)
  check p Wire {..}
    | member w'key omap = let (gate, _) = omap ~> w'key in p gate
    | otherwise = False
{-# INLINEABLE amplify'gate #-}

-- | Create an amplifier gate with the given in/out wires
amplify :: Num a => Bool -> Wire a -> IO (Wire a, [Gate a])
amplify pass in'
  | pass = pure (in', [])
  | otherwise = do
      out <- rand'wire
      pure (out, [Gate Mul in' amplifier out])
{-# INLINE amplify #-}
