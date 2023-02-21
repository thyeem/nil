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

-- | Lookup table used in reorg process
type O'table f = Map String (Gate f, Int)

(+++) :: Applicative f => f [a] -> f [a] -> f [a]
(+++) = liftA2 (++)
{-# INLINE (+++) #-}

-- | Inspect operators
valid'operator :: Gate f -> Bool
valid'operator Gate {..} = g'op `elem` [Mul, Add, End]
{-# INLINE valid'operator #-}

-- | When merge happens
needs'merge :: Gate f -> Bool
needs'merge g@Gate {..} =
  w'recip g'rwire
    || (and' out'wirep g && g'op == Mul)
{-# INLINE needs'merge #-}

-- | Create a helper knot wire having a hashed unique key
rand'wire :: Num f => IO (Wire f)
rand'wire =
  set'expr "rand-tie"
    . unit'var
    . ("~x" ++)
    <$> random'hex 8
{-# INLINE rand'wire #-}

-- | Toggle the reciprocal flag
recip' :: Wire f -> Wire f
recip' wire@Wire {..} = wire {w'recip = not w'recip}
{-# INLINE recip' #-}

-- | Determine which wire will be cut: in forms of (survived, killed)
tip'cut :: O'table f -> String -> (Wire f, Wire f)
tip'cut table key =
  let (Gate {g'lwire, g'rwire}, _) = table ~> key
      height wire
        | member (w'key wire) table = snd (table ~> w'key wire)
        | otherwise = -1
   in if w'recip g'rwire || (height g'lwire > height g'rwire)
        then (g'lwire, g'rwire)
        else (g'rwire, g'lwire)
{-# INLINE tip'cut #-}

-- | nil-circuit
reorg'circuit :: (Eq f, Num f, Show f) => Circuit f -> IO (Circuit f)
reorg'circuit circuit@Circuit {..} = do
  let key = w'key . g'owire . last $ c'gates
  reorged <- nub <$> reorg (otab'from'gates c'gates) key
  shifted <- concat <$> mapM shift'gate reorged
  gates <- concat <$> mapM (amplify'gate (otab'from'gates shifted)) shifted
  pure $ circuit {c'gates = gates}
{-# INLINE reorg'circuit #-}

-- | Generate a lookup table used in circuit reorg process.
otab'from'gates :: [Gate f] -> O'table f
otab'from'gates = foldl' update mempty
 where
  update table g@Gate {..} =
    let height = max (find g'lwire) (find g'rwire)
        find Wire {w'key}
          | member w'key table = 1 + snd (table ~> w'key)
          | otherwise = 1
     in insert (w'key g'owire) (g, height) table
{-# INLINE otab'from'gates #-}

-- | Reconstruct gates and wires of a given circuit for use of nilsign
reorg :: (Eq f, Num f, Show f) => O'table f -> String -> IO [Gate f]
reorg table key
  | member key table = do
      let (g@Gate {..}, _) = table ~> key
          (tip, cut) = tip'cut table key
      if
          | not . valid'operator $ g ->
              die $ "Error, found invalid op during reorg: " ++ show g'op
          | needs'merge g ->
              reorg table (w'key tip) +++ merge table g'owire tip cut
          | otherwise ->
              reorg table (w'key tip) +++ reorg table (w'key cut) +++ pure [g]
  | otherwise = pure []
{-# INLINEABLE reorg #-}

-- | merge
merge :: (Eq f, Num f) => O'table f -> Wire f -> Wire f -> Wire f -> IO [Gate f]
merge table out tip cut
  | member (w'key cut) table = do
      let (Gate {g'op}, _) = table ~> w'key cut
      case g'op of
        Mul -> merge'mul table out tip cut
        Add -> merge'add table out tip cut
        op -> die $ "Error, unexpected operator: " ++ show op
  | otherwise = pure [Gate Mul tip cut out]
{-# INLINEABLE merge #-}

merge'mul :: (Eq f, Num f) => O'table f -> Wire f -> Wire f -> Wire f -> IO [Gate f]
merge'mul table out tip cut = do
  let op = if w'recip cut then recip' else id
      (tip_, cut_) = bimap op op $ tip'cut table (w'key cut)
  tie <- rand'wire
  merge table tie tip tip_ +++ merge table out tie cut_
{-# INLINEABLE merge'mul #-}

merge'add :: (Eq f, Num f) => O'table f -> Wire f -> Wire f -> Wire f -> IO [Gate f]
merge'add table out tip cut = do
  if w'recip cut
    then
      die . unlines $
        [ "Error, failed to reorg the wire in circuit: " ++ w'expr cut
        , "A divisor of (/) should be a const value when it is involved with (+)"
        ]
    else do
      let (tip_, cut_) = tip'cut table (w'key cut)
      tie'a <- rand'wire
      tie'b <- rand'wire
      merge table tie'a tip tip_
        +++ merge table tie'b tip cut_
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
shift'wirep :: Wire f -> Bool
shift'wirep Wire {..} =
  w'key == const'key
    && w'expr == shift'expr
{-# INLINE shift'wirep #-}

-- | Predicate for a amplifier-knot
amp'wirep :: Wire f -> Bool
amp'wirep Wire {..} =
  w'key == const'key
    && w'expr == amp'expr
{-# INLINE amp'wirep #-}

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

frozen'wirep :: Wire f -> Bool
frozen'wirep Wire {..} = w'expr == frozen'expr
{-# INLINE frozen'wirep #-}

freeze :: Wire f -> Wire f
freeze = set'expr frozen'expr . set'key const'key
{-# INLINE freeze #-}

shifter :: Num f => Wire f
shifter = set'expr shift'expr unit'const
{-# INLINE shifter #-}

amplifier :: Num f => Wire f
amplifier = set'expr amp'expr unit'const
{-# INLINE amplifier #-}

-- | Add shifting gates to each entry gate
shift'gate :: Num f => Gate f -> IO [Gate f]
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
shift :: Num f => Gateop -> Wire f -> Wire f -> Wire f -> IO [Gate f]
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
amplify'gate :: Num f => O'table f -> Gate f -> IO [Gate f]
amplify'gate table g@Gate {g'lwire, g'rwire, g'owire, g'op = op}
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
    | member w'key table = let (gate, _) = table ~> w'key in p gate
    | otherwise = False
{-# INLINEABLE amplify'gate #-}

-- | Create an amplifier gate with the given in/out wires
amplify :: Num f => Bool -> Wire f -> IO (Wire f, [Gate f])
amplify pass in'
  | pass = pure (in', [])
  | otherwise = do
      out <- rand'wire
      pure (out, [Gate Mul in' amplifier out])
{-# INLINE amplify #-}
