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
type Omap r = Map String (Gate r, Int)

(+++) :: Applicative f => f [a] -> f [a] -> f [a]
(+++) = liftA2 (++)
{-# INLINE (+++) #-}

-- | Test logical operator (AND) with a predicate and input wires
and' :: (Wire r -> Bool) -> Gate r -> Bool
and' p Gate {..} = p g'lwire && p g'rwire
{-# INLINE and' #-}

-- | Test logical operator (XOR) with a predicate and input wires
xor' :: (Wire r -> Bool) -> Gate r -> Bool
xor' p g = not (and' p g) && not (nor' p g)
{-# INLINE xor' #-}

-- | Test logical operator (NOR) with a predicate and input wires
nor' :: (Wire r -> Bool) -> Gate r -> Bool
nor' p Gate {..} = not $ p g'lwire || p g'rwire
{-# INLINE nor' #-}

{- | Classfy input wires satisfying the given predicate: (pass, fail)
   The result is valid only when applied input wires hold XOR
-}
either'by :: (Wire r -> Bool) -> Gate r -> (Wire r, Wire r)
either'by p g@Gate {..}
  | xor' p g = if p g'lwire then (g'lwire, g'rwire) else (g'rwire, g'lwire)
  | otherwise =
      die $
        unwords ["Error, not XOR between:", w'key g'lwire, "and", w'key g'rwire]

-- | Inspect operators
valid'operator :: Gate r -> Bool
valid'operator Gate {..} = g'op `elem` [Mul, Add, End]
{-# INLINE valid'operator #-}

-- | When merge happens
needs'merge :: Gate r -> Bool
needs'merge g@Gate {..} =
  w'recip g'rwire
    || (and' out'wirep g && g'op == Mul)
{-# INLINE needs'merge #-}

-- | Create a helper knot wire having a hashed unique key
rand'wire :: Num r => IO (Wire r)
rand'wire =
  set'expr "rand-tie"
    . unit'var
    . ("~x" ++)
    <$> random'hex 8
{-# INLINE rand'wire #-}

-- | Toggle the reciprocal flag
recip' :: Wire r -> Wire r
recip' wire@Wire {..} = wire {w'recip = not w'recip}
{-# INLINE recip' #-}

-- | Determine which wire will be cut: in forms of (survived, killed)
tip'cut :: Omap r -> String -> (Wire r, Wire r)
tip'cut map key =
  let (Gate {g'lwire, g'rwire}, _) = map ~> key
      height wire
        | member (w'key wire) map = snd (map ~> w'key wire)
        | otherwise = -1
   in if w'recip g'rwire || (height g'lwire > height g'rwire)
        then (g'lwire, g'rwire)
        else (g'rwire, g'lwire)
{-# INLINE tip'cut #-}

-- | nil-circuit
reorg'circuit :: (Eq r, Num r, Show r) => Circuit r -> IO (Circuit r)
reorg'circuit circuit@Circuit {..} = do
  let key = w'key . g'owire . last $ c'gates
  reorged <- nub <$> reorg (omap'from'gates c'gates) key
  shifted <- concat <$> mapM shift'gate reorged
  gates <- concat <$> mapM (amplify'gate (omap'from'gates shifted)) shifted
  pure $ circuit {c'gates = gates}
{-# INLINE reorg'circuit #-}

-- | Generate a Omap used in circuit reorg process.
omap'from'gates :: [Gate r] -> Omap r
omap'from'gates = foldl' update mempty
 where
  update map g@Gate {..} =
    let height = max (find g'lwire) (find g'rwire)
        find Wire {w'key}
          | member w'key map = 1 + snd (map ~> w'key)
          | otherwise = 1
     in insert (w'key g'owire) (g, height) map
{-# INLINE omap'from'gates #-}

-- | Reconstruct gates and wires of a given circuit for use of nilsign
reorg :: (Eq r, Num r, Show r) => Omap r -> String -> IO [Gate r]
reorg map key
  | member key map = do
      let (g@Gate {..}, _) = map ~> key
          (tip, cut) = tip'cut map key
      if
          | not . valid'operator $ g ->
              die $ "Error, found invalid op during reorg: " ++ show g'op
          | needs'merge g ->
              reorg map (w'key tip) +++ merge map g'owire tip cut
          | otherwise ->
              reorg map (w'key tip) +++ reorg map (w'key cut) +++ pure [g]
  | otherwise = pure []
{-# INLINEABLE reorg #-}

-- | merge
merge :: (Eq r, Num r) => Omap r -> Wire r -> Wire r -> Wire r -> IO [Gate r]
merge map out tip cut
  | member (w'key cut) map = do
      let (Gate {g'op}, _) = map ~> w'key cut
      case g'op of
        Mul -> merge'mul map out tip cut
        Add -> merge'add map out tip cut
        op -> die $ "Error, unexpected operator: " ++ show op
  | otherwise = pure [Gate Mul tip cut out]
{-# INLINEABLE merge #-}

merge'mul :: (Eq r, Num r) => Omap r -> Wire r -> Wire r -> Wire r -> IO [Gate r]
merge'mul map out tip cut = do
  let op = if w'recip cut then recip' else id
      (tip_, cut_) = bimap op op $ tip'cut map (w'key cut)
  tie <- rand'wire
  merge map tie tip tip_ +++ merge map out tie cut_
{-# INLINEABLE merge'mul #-}

merge'add :: (Eq r, Num r) => Omap r -> Wire r -> Wire r -> Wire r -> IO [Gate r]
merge'add map out tip cut = do
  if w'recip cut
    then
      die . unlines $
        [ "Error, failed to reorg the wire in circuit: " ++ w'expr cut
        , "A divisor of (/) should be a const value when it is involved with (+)"
        ]
    else do
      let (tip_, cut_) = tip'cut map (w'key cut)
      tie'a <- rand'wire
      tie'b <- rand'wire
      merge map tie'a tip tip_
        +++ merge map tie'b tip cut_
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

-- | Predicate for a delta-shifter
shift'wirep :: Wire r -> Bool
shift'wirep Wire {..} =
  w'key == const'key
    && w'expr == shift'expr
{-# INLINE shift'wirep #-}

-- | Predicate for a amplifier-knot
amp'wirep :: Wire r -> Bool
amp'wirep Wire {..} =
  w'key == const'key
    && w'expr == amp'expr
{-# INLINE amp'wirep #-}

entry'wirep :: Wire r -> Bool
entry'wirep wire =
  and $
    [ not . out'wirep
    , not . shift'wirep
    , not . amp'wirep
    , not . frozen'wirep
    ]
      <*> [wire]
{-# INLINE entry'wirep #-}

frozen'wirep :: Wire r -> Bool
frozen'wirep Wire {..} = w'expr == frozen'expr
{-# INLINE frozen'wirep #-}

freeze :: Wire r -> Wire r
freeze = set'expr frozen'expr . set'key const'key
{-# INLINE freeze #-}

shifter :: Num r => Wire r
shifter = set'expr shift'expr unit'const
{-# INLINE shifter #-}

amplifier :: Num r => Wire r
amplifier = set'expr amp'expr unit'const
{-# INLINE amplifier #-}

-- | Add shifting gates to each entry gate
shift'gate :: Num r => Gate r -> IO [Gate r]
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
shift :: Num r => Gateop -> Wire r -> Wire r -> Wire r -> IO [Gate r]
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
amplify'gate :: Num r => Omap r -> Gate r -> IO [Gate r]
amplify'gate map g@Gate {g'lwire, g'rwire, g'owire, g'op = op}
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
    | member w'key map = let (gate, _) = map ~> w'key in p gate
    | otherwise = False
{-# INLINEABLE amplify'gate #-}

-- | Create an amplifier gate with the given in/out wires
amplify :: Num r => Bool -> Wire r -> IO (Wire r, [Gate r])
amplify pass in'
  | pass = pure (in', [])
  | otherwise = do
      out <- rand'wire
      pure (out, [Gate Mul in' amplifier out])
{-# INLINE amplify #-}
