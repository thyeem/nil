{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Nil.Reorg where

import Control.Applicative (liftA2)
import Data.Bifunctor (bimap)
import Data.Bits (xor)
import Data.Functor ((<&>))
import Data.List (foldl', nub)
import Data.Map (Map, insert, member, (!?))
import Data.Maybe (fromMaybe)
import Nil.Circuit
  ( Circuit (..)
  , Gate (..)
  , Gateop (..)
  , Wire (..)
  , and'
  , nor'
  , out'wirep
  , recip'wirep
  , set'expr
  , set'key
  , set'unit'key
  , set'unit'val
  , unit'wire
  , xor'
  )
import Nil.Utils (die, random'hex)

-- | Lookup table used in reorg process
type O'table f = Map String (Gate f, Int)

-- | Get a record from O'table
(<!>) :: O'table f -> String -> (Gate f, Int)
(<!>) table key =
  fromMaybe (die $ "Error, not found key: " ++ key) $ table !? key
{-# INLINE (<!>) #-}

(+++) :: Applicative f => f [a] -> f [a] -> f [a]
(+++) = liftA2 (++)
{-# INLINE (+++) #-}

-- | The name prepared wire representing delta-shift
delta'expr :: String
delta'expr = ">>"
{-# INLINE delta'expr #-}

-- | Predicate for a delta-shifter
delta'wirep :: Wire f -> Bool
delta'wirep Wire {..} = w'expr == delta'expr

-- | Inspect operators
valid'operator :: Gate f -> Bool
valid'operator Gate {..} = g'op `elem` [Mul, Add, End]
{-# INLINE valid'operator #-}

-- | When merge happens
needs'merge :: Gate f -> Bool
needs'merge g@Gate {..} =
  recip'wirep g'rwire
    || (and' out'wirep g && g'op == Mul)
{-# INLINE needs'merge #-}

-- | Create a helper knot wire having a hashed unique key
rand'wire :: Num f => IO (Wire f)
rand'wire =
  set'expr "reorged"
    . set'unit'key
    . ("~x" ++)
    <$> random'hex 8
{-# INLINE rand'wire #-}

-- | Toggle the reciprocal flag
recip' :: Wire f -> Wire f
recip' wire@Wire {..} = wire {w'flag = 1 `xor` w'flag}
{-# INLINE recip' #-}

-- | Determine which wire will be cut: in forms of (survived, killed)
tip'cut :: O'table f -> String -> (Wire f, Wire f)
tip'cut table key =
  let (Gate {g'lwire, g'rwire}, _) = table <!> key
      height wire
        | member (w'key wire) table = snd (table <!> w'key wire)
        | otherwise = -1
   in if recip'wirep g'rwire || (height g'lwire > height g'rwire)
        then (g'lwire, g'rwire)
        else (g'rwire, g'lwire)
{-# INLINE tip'cut #-}

-- | reorg-circuit
reorg'circuit :: (Eq f, Num f, Show f) => Circuit f -> IO (Circuit f)
reorg'circuit circuit@Circuit {..} = do
  gates <-
    reorg
      (gen'table c'gates)
      (w'key . g'owire . last $ c'gates)
      >>= mapM shift'entries
      <&> nub . concat
  pure $ circuit {c'gates = gates}
{-# INLINE reorg'circuit #-}

-- | Generate a lookup table used in circuit reorg process.
gen'table :: [Gate f] -> O'table f
gen'table = foldl' update mempty
 where
  update table g@Gate {..} =
    let height = max (find g'lwire) (find g'rwire)
        find wire
          | member (w'key wire) table = 1 + snd (table <!> w'key wire)
          | otherwise = 1
     in insert (w'key g'owire) (g, height) table
{-# INLINE gen'table #-}

-- | Reorganize a circuit for use of zksign
reorg :: (Eq f, Num f, Show f) => O'table f -> String -> IO [Gate f]
reorg table key
  | member key table = do
      let (g@Gate {..}, _) = table <!> key
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
      let (Gate {g'op}, _) = table <!> w'key cut
      case g'op of
        Mul -> merge'mul table out tip cut
        Add -> merge'add table out tip cut
        op -> die $ "Error, unexpected operator: " ++ show op
  | otherwise = pure [Gate Mul tip cut out]
{-# INLINEABLE merge #-}

merge'mul :: (Eq f, Num f) => O'table f -> Wire f -> Wire f -> Wire f -> IO [Gate f]
merge'mul table out tip cut = do
  let op = if recip'wirep cut then recip' else id
      (tip_, cut_) = bimap op op $ tip'cut table (w'key cut)
  tie <- rand'wire
  merge table tie tip tip_ +++ merge table out tie cut_
{-# INLINEABLE merge'mul #-}

merge'add :: (Eq f, Num f) => O'table f -> Wire f -> Wire f -> Wire f -> IO [Gate f]
merge'add table out tip cut = do
  if recip'wirep cut
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

shift'entries :: Num f => Gate f -> IO [Gate f]
shift'entries g@Gate {..}
  | g'op == End = pure [g]
  | xor' out'wirep g = shift g'op g'lwire g'rwire g'owire
  | nor' out'wirep g = do
      tie <- rand'wire
      shift Mul g'lwire unit'wire tie +++ shift g'op g'rwire tie g'owire
  | otherwise = pure [g]
{-# INLINEABLE shift'entries #-}

shift :: Num f => Gateop -> Wire f -> Wire f -> Wire f -> IO [Gate f]
shift op lwire rwire owire = do
  tie'a <- rand'wire
  tie'b <- rand'wire
  pure [Gate op lwire rwire tie'a]
    +++ pure [Gate Mul tie'a (set'expr delta'expr $ set'unit'val 0) tie'b]
    +++ pure [Gate Add tie'a tie'b owire]
{-# INLINEABLE shift #-}
