{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif

-- | This module contains the Reflex interface, as well as a variety of
-- convenience functions for working with 'Event's, 'Behavior's, and other
-- signals.
module Reflex.Basics
  ( module Reflex.Patch
    -- * Primitives
  , module Reflex.Sig
  , coerceBehavior
  , coerceEvent
  , coerceDynamic
  , MonadSample (..)
  , MonadHold (..)
    -- ** 'fan'-related types
    -- ** 'Incremental'-related types
    -- * Convenience functions
  , constDyn
  , pushAlways
    -- ** Combining 'Event's
  , leftmost
  , mergeMap
  , mergeList
  , mergeWith
  , difference
    -- ** Breaking up 'Event's
  , splitE
  , fanEither
  , fanThese
  , fanMap
  , dmapToThese
  , EitherTag (..)
  , eitherToDSum
  , dsumToEither
    -- ** Switching between 'Event's
  , switchPromptly
  , switchPromptOnly
    -- ** Using 'Event's to sample 'Behavior's
  , tag
  , attach
  , attachWith
  , attachWithMaybe
    -- ** Blocking an 'Event' based on a 'Behavior'
  , gate
    -- ** Combining 'Dynamic's
  , distributeDMapOverDynPure
  , distributeListOverDyn
  , distributeListOverDynWith
  , zipDyn
  , zipDynWith
    -- ** Accumulating state
  , Accumulator (..)
  , mapAccum_
  , mapAccumM_
  , mapAccumMaybe_
  , mapAccumMaybeM_
  , zipListWithEvent
  , headE
  , tailE
  , headTailE
  , switcher
    -- * Debugging functions
  , traceEvent
  , traceEventWith
    -- * Unsafe functions
  , unsafeDynamic
    -- * 'FunctorMaybe'
  , FunctorMaybe (..)
  , fforMaybe
  , ffilter
    -- * Miscellaneous convenience functions
  , ffor
  , MonadAdjust (..)
    -- * Deprecated functions
  , appendEvents
  , onceE
  , sequenceThese
  , fmapMaybeCheap
  , fmapCheap
  , fforCheap
  , fforMaybeCheap
  , pushAlwaysCheap
  , tagCheap
  , mergeWithCheap
  , mergeWithCheap'
  ) where

import Control.Applicative
import Control.Monad.Identity hiding (forM, forM_, mapM, mapM_, sequence, sequence_)
import Control.Monad.Reader hiding (forM, forM_, mapM, mapM_, sequence, sequence_)
import Data.Align
import Data.Bifunctor
import Data.Coerce
import Data.Dependent.Map (DMap, DSum (..), GCompare (..))
import qualified Data.Dependent.Map as DMap
import Data.Either
import Data.Foldable
import Data.Functor.Bind hiding (join)
import qualified Data.Functor.Bind as Bind
import Data.Functor.Misc
import Data.Functor.Plus
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Maybe
import Data.Monoid hiding (Alt, (<>))
import Data.Semigroup (Semigroup, sconcat, stimes, (<>))
import Data.String
import Data.These
import Data.Traversable
import Data.Type.Coercion
import Reflex.FunctorMaybe
import Reflex.Patch

import Reflex.Sig

-- Note: must come last to silence warnings due to AMP on GHC < 7.10
import Prelude hiding (foldl, mapM, mapM_, sequence, sequence_)

import Debug.Trace (trace)

-- | Coerce a 'Behavior' between representationally-equivalent value types
coerceBehavior :: (HasTimeline t, Coercible a b) => Behavior t a -> Behavior t b
coerceBehavior = coerceWith $ behaviorCoercion Coercion

-- | Coerce an 'Event' between representationally-equivalent occurrence types
coerceEvent :: (HasTimeline t, Coercible a b) => Event t a -> Event t b
coerceEvent = coerceWith $ eventCoercion Coercion

-- | Coerce a 'Dynamic' between representationally-equivalent value types
coerceDynamic :: (HasTimeline t, Coercible a b) => Dynamic t a -> Dynamic t b
coerceDynamic = coerceWith $ dynamicCoercion Coercion

-- | Construct a 'Dynamic' from a 'Behavior' and an 'Event'.  The 'Behavior'
-- _must_ change when and only when the 'Event' fires, such that the
-- 'Behavior''s value is always equal to the most recent firing of the 'Event';
-- if this is not the case, the resulting 'Dynamic' will behave
-- nondeterministically.
unsafeDynamic :: HasTimeline t => Behavior t a -> Event t a -> Dynamic t a
unsafeDynamic = unsafeBuildDynamic . sample

-- | Construct a 'Dynamic' value that never changes
constDyn :: HasTimeline t => a -> Dynamic t a
constDyn = pure

--------------------------------------------------------------------------------
-- Convenience functions
--------------------------------------------------------------------------------

-- | Create an 'Event' from another 'Event'.  The provided function can sample
-- 'Behavior's and hold 'Event's.
pushAlways :: HasTimeline t => (a -> PushM t b) -> Event t a -> Event t b
pushAlways f = push (fmap Just . f)

-- | Flipped version of 'fmap'.
ffor :: Functor f => f a -> (a -> b) -> f b
ffor = flip fmap

instance HasTimeline t => Applicative (Behavior t) where
  pure = constant
  f <*> x = pull $ sample f `ap` sample x
  _ *> b = b
  a <* _ = a

instance HasTimeline t => Apply (Behavior t) where
  (<.>) = (<*>)

instance HasTimeline t => Bind (Behavior t) where
  (>>-) = (>>=)

instance (HasTimeline t, Fractional a) => Fractional (Behavior t a) where
  (/) = liftA2 (/)
  fromRational = pure . fromRational
  recip = fmap recip

instance HasTimeline t => Functor (Behavior t) where
  fmap f = pull . fmap f . sample

instance (HasTimeline t, IsString a) => IsString (Behavior t a) where
  fromString = pure . fromString

instance HasTimeline t => Monad (Behavior t) where
  a >>= f = pull $ sample a >>= sample . f
  -- Note: it is tempting to write (_ >> b = b); however, this would result in (fail x >> return y) succeeding (returning y), which violates the law that (a >> b = a >>= \_ -> b), since the implementation of (>>=) above actually will fail.  Since we can't examine 'Behavior's other than by using sample, I don't think it's possible to write (>>) to be more efficient than the (>>=) above.
  return = constant
  fail = error "Monad (Behavior t) does not support fail"

instance (HasTimeline t, Monoid a) => Monoid (Behavior t a) where
  mempty = constant mempty
  mappend a b = pull $ liftM2 mappend (sample a) (sample b)
  mconcat = pull . fmap mconcat . mapM sample

instance (HasTimeline t, Num a) => Num (Behavior t a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  fromInteger = pure . fromInteger
  negate = fmap negate
  signum = fmap signum

instance (HasTimeline t, Semigroup a) => Semigroup (Behavior t a) where
  a <> b = pull $ liftM2 (<>) (sample a) (sample b)
  sconcat = pull . fmap sconcat . mapM sample
#if MIN_VERSION_semigroups(0,17,0)
  stimes n = fmap $ stimes n
#else
  times1p n = fmap $ times1p n
#endif

-- | Flipped version of 'fmapMaybe'.
fforMaybe :: FunctorMaybe f => f a -> (a -> Maybe b) -> f b
fforMaybe = flip fmapMaybe

-- | Filter 'f a' using the provided predicate.
-- Relies on 'fforMaybe'.
ffilter :: FunctorMaybe f => (a -> Bool) -> f a -> f a
ffilter f = fmapMaybe $ \x -> if f x then Just x else Nothing

-- | Left-biased event union (prefers left event on simultaneous
-- occurrence).
instance HasTimeline t => Alt (Event t) where
  ev1 <!> ev2 = leftmost [ev1, ev2]

-- | 'Event' intersection (convenient interface to 'coincidence').
instance HasTimeline t => Apply (Event t) where
  evf <.> evx = coincidence (fmap (<$> evx) evf)

-- | 'Event' intersection (convenient interface to 'coincidence').
instance HasTimeline t => Bind (Event t) where
  evx >>- f = coincidence (f <$> evx)
  join = coincidence

instance HasTimeline t => Functor (Event t) where
  {-# INLINE fmap #-}
  fmap f = fmapMaybe $ Just . f

instance HasTimeline t => FunctorMaybe (Event t) where
  {-# INLINE fmapMaybe #-}
  fmapMaybe f = push $ return . f

-- | Never: @'zero' = 'never'@.
instance HasTimeline t => Plus (Event t) where
  zero = never

-- | Replace each occurrence value of the 'Event' with the value of the
-- 'Behavior' at the time of that occurrence.
tag :: HasTimeline t => Behavior t b -> Event t a -> Event t b
tag b = pushAlways $ \_ -> sample b

-- | Create a new 'Event' that combines occurences of supplied 'Event' with the
-- current value of the 'Behavior'.
attach :: HasTimeline t => Behavior t a -> Event t b -> Event t (a, b)
attach = attachWith (,)

-- | Create a new 'Event' that occurs when the supplied 'Event' occurs by
-- combining it with the current value of the 'Behavior'.
attachWith :: HasTimeline t => (a -> b -> c) -> Behavior t a -> Event t b -> Event t c
attachWith f = attachWithMaybe $ \a b -> Just $ f a b

-- | Create a new 'Event' by combining each occurence with the current value of
-- the 'Behavior'. The occurrence is discarded if the combining function returns
-- Nothing
attachWithMaybe :: HasTimeline t => (a -> b -> Maybe c) -> Behavior t a -> Event t b -> Event t c
attachWithMaybe f b e = flip push e $ \o -> (`f` o) <$> sample b

-- | Create a new 'Event' that only occurs only once, on the first occurence of
-- the supplied 'Event'.
headE :: (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => Event t a -> m (Event t a)
headE e = do
  rec be <- hold e $ fmap (const never) e'
      let e' = switch be
  return e'

-- | Create a new 'Event' that occurs on all but the first occurence of the
-- supplied 'Event'.
tailE :: (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => Event t a -> m (Event t a)
tailE e = snd <$> headTailE e

-- | Create a tuple of two 'Event's with the first one occuring only the first
-- time the supplied 'Event' occurs and the second occuring on all but the first
-- occurence.
headTailE :: (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => Event t a -> m (Event t a, Event t a)
headTailE e = do
  eHead <- headE e
  be <- hold never $ fmap (const e) eHead
  return (eHead, switch be)

-- | Split the supplied 'Event' into two individual 'Event's occuring at the
-- same time with the respective values from the tuple.
splitE :: HasTimeline t => Event t (a, b) -> (Event t a, Event t b)
splitE e = (fmap fst e, fmap snd e)

-- | Print the supplied 'String' and the value of the 'Event' on each
-- occurence. This should /only/ be used for debugging.
--
-- Note: As with Debug.Trace.trace, the message will only be printed if the
-- 'Event' is actually used.
traceEvent :: (HasTimeline t, Show a) => String -> Event t a -> Event t a
traceEvent s = traceEventWith $ \x -> s <> ": " <> show x

-- | Print the output of the supplied function on each occurence of the
-- 'Event'. This should /only/ be used for debugging.
--
-- Note: As with Debug.Trace.trace, the message will only be printed if the
-- 'Event' is actually used.
traceEventWith :: HasTimeline t => (a -> String) -> Event t a -> Event t a
traceEventWith f = push $ \x -> trace (f x) $ return $ Just x

instance (Semigroup a, HasTimeline t) => Semigroup (Event t a) where
  (<>) = alignWith (mergeThese (<>))
  sconcat = fmap sconcat . mergeList . toList
#if MIN_VERSION_semigroups(0,17,0)
  stimes n = fmap $ stimes n
#else
  times1p n = fmap $ times1p n
#endif

instance (Semigroup a, HasTimeline t) => Monoid (Event t a) where
  mempty = never
  mappend = (<>)
  mconcat = fmap sconcat . mergeList

-- | Create a new 'Event' that occurs if at least one of the 'Event's in the
-- list occurs. If multiple occur at the same time they are folded from the left
-- with the given function.
{-# INLINE mergeWith #-}
mergeWith :: HasTimeline t => (a -> a -> a) -> [Event t a] -> Event t a
mergeWith = mergeWith' id

{-# INLINE mergeWith' #-}
mergeWith' :: HasTimeline t => (a -> b) -> (b -> b -> b) -> [Event t a] -> Event t b
mergeWith' f g es = fmap (Prelude.foldl1 g . map (\(Const2 _ :=> Identity v) -> f v) . DMap.toList)
                  . merge
                  . DMap.fromDistinctAscList
                  . map (\(k, v) -> Const2 k :=> v)
                  $ zip [0 :: Int ..] es

-- | Create a new 'Event' that occurs if at least one of the 'Event's in the
-- list occurs. If multiple occur at the same time the value is the value of the
-- leftmost event.
{-# INLINE leftmost #-}
leftmost :: HasTimeline t => [Event t a] -> Event t a
leftmost = mergeWith const

-- | Create a new 'Event' that occurs if at least one of the 'Event's in the
-- list occurs and has a list of the values of all 'Event's occuring at that
-- time.
mergeList :: HasTimeline t => [Event t a] -> Event t (NonEmpty a)
mergeList [] = never
mergeList es = mergeWithCheap' (:|[]) (<>) es

-- | Create a new 'Event' combining the map of 'Event's into an 'Event' that
-- occurs if at least one of them occurs and has a map of values of all 'Event's
-- occuring at that time.
mergeMap :: (HasTimeline t, Ord k) => Map k (Event t a) -> Event t (Map k a)
mergeMap = fmap dmapToMap . merge . mapWithFunctorToDMap

-- | Split the event into separate events for 'Left' and 'Right' values.
fanEither :: HasTimeline t => Event t (Either a b) -> (Event t a, Event t b)
fanEither e =
  let justLeft = either Just (const Nothing)
      justRight = either (const Nothing) Just
  in (fmapMaybe justLeft e, fmapMaybe justRight e)

-- | Split the event into separate events for 'This' and 'That' values,
-- allowing them to fire simultaneously when the input value is 'These'.
fanThese :: HasTimeline t => Event t (These a b) -> (Event t a, Event t b)
fanThese e =
  let this (This x) = Just x
      this (These x _) = Just x
      this _ = Nothing
      that (That y) = Just y
      that (These _ y) = Just y
      that _ = Nothing
  in (fmapMaybe this e, fmapMaybe that e)

-- | Split the event into an 'EventSelector' that allows efficient selection of
-- the individual 'Event's.
fanMap :: (HasTimeline t, Ord k) => Event t (Map k a) -> EventSelector t (Const2 k a)
fanMap = fan . fmap mapToDMap

-- | Switches to the new event whenever it receives one.  Whenever a new event
-- is provided, if it is firing, its value will be the resulting event's value;
-- if it is not firing, but the old one is, the old one's value will be used.
switchPromptly :: (HasTimeline t, MonadHold (Impl t) m) => Event t a -> Event t (Event t a) -> m (Event t a)
switchPromptly ea0 eea = do
  bea <- hold ea0 eea
  let eLag = switch bea
      eCoincidences = coincidence eea
  return $ leftmost [eCoincidences, eLag]

-- | 'switch'es to a new event whenever it receives one.  At the moment of
-- switching, the old event will be ignored if it fires, and the new one will be
-- used if it fires; this is the opposite of 'switch', which will use only the
-- old value.
switchPromptOnly :: (HasTimeline t, MonadHold (Impl t) m) => Event t a -> Event t (Event t a) -> m (Event t a)
switchPromptOnly e0 e' = do
  eLag <- switch <$> hold e0 e'
  return $ coincidence $ leftmost [e', eLag <$ eLag]

instance HasTimeline t => Align (Event t) where
  nil = never
  align = alignWithMaybe Just

-- | Create a new 'Event' that only occurs if the supplied 'Event' occurs and
-- the 'Behavior' is true at the time of occurence.
gate :: HasTimeline t => Behavior t Bool -> Event t a -> Event t a
gate = attachWithMaybe $ \allow a -> if allow then Just a else Nothing

-- | Create a new behavior given a starting behavior and switch to a the behvior
--   carried by the event when it fires.
switcher :: (HasTimeline t, MonadHold (Impl t) m)
        => Behavior t a -> Event t (Behavior t a) -> m (Behavior t a)
switcher b eb = pull . (sample <=< sample) <$> hold b eb

-- | Combine two 'Dynamic's.  The result will change whenever either (or both)
-- input 'Dynamic' changes.  Equivalent to @zipDynWith (,)@.
zipDyn :: HasTimeline t => Dynamic t a -> Dynamic t b -> Dynamic t (a, b)
zipDyn = zipDynWith (,)

-- | Combine two 'Dynamic's with a combining function.  The result will change
-- whenever either (or both) input 'Dynamic' changes.
-- More efficient than liftA2.
zipDynWith :: HasTimeline t => (a -> b -> c) -> Dynamic t a -> Dynamic t b -> Dynamic t c
zipDynWith f da db =
  let eab = align (updated da) (updated db)
      ec = flip push eab $ \o -> do
        (a, b) <- case o of
          This a -> do
            b <- sample $ current db
            return (a, b)
          That b -> do
            a <- sample $ current da
            return (a, b)
          These a b -> return (a, b)
        return $ Just $ f a b
  in unsafeBuildDynamic (f <$> sample (current da) <*> sample (current db)) ec

instance (HasTimeline t, Monoid a) => Monoid (Dynamic t a) where
  mconcat = distributeListOverDynWith mconcat
  mempty = constDyn mempty
  mappend = zipDynWith mappend

-- | This function converts a 'DMap' whose elements are 'Dynamic's into a
-- 'Dynamic' 'DMap'.  Its implementation is more efficient than doing the same
-- through the use of multiple uses of 'zipWithDyn' or 'Applicative' operators.
distributeDMapOverDynPure :: forall t k. (HasTimeline t, GCompare k) => DMap k (Dynamic t) -> Dynamic t (DMap k Identity)
distributeDMapOverDynPure dm = case DMap.toList dm of
  [] -> constDyn DMap.empty
  [k :=> v] -> fmap (DMap.singleton k . Identity) v
  _ ->
    let getInitial = DMap.traverseWithKey (\_ -> fmap Identity . sample . current) dm
        edmPre = merge $ DMap.map updated dm
        result = unsafeBuildDynamic getInitial $ flip pushAlways edmPre $ \news -> do
          olds <- sample $ current result
          return $ DMap.unionWithKey (\_ _ new -> new) olds news
    in result

-- | Convert a list of 'Dynamic's into a 'Dynamic' list.
distributeListOverDyn :: HasTimeline t => [Dynamic t a] -> Dynamic t [a]
distributeListOverDyn = distributeListOverDynWith id

-- | Create a new 'Dynamic' by applying a combining function to a list of 'Dynamic's
distributeListOverDynWith :: HasTimeline t => ([a] -> b) -> [Dynamic t a] -> Dynamic t b
distributeListOverDynWith f = fmap (f . map (\(Const2 _ :=> Identity v) -> v) . DMap.toList) . distributeDMapOverDynPure . DMap.fromList . map (\(k, v) -> Const2 k :=> v) . zip [0 :: Int ..]

-- | Create a new 'Event' that occurs when the first supplied 'Event' occurs
-- unless the second supplied 'Event' occurs simultaneously.
difference :: HasTimeline t => Event t a -> Event t b -> Event t a
difference = alignWithMaybe $ \case
  This a -> Just a
  _      -> Nothing

-- (intentially not exported, for now)
alignWithMaybe
  :: HasTimeline t => (These a b -> Maybe c) -> Event t a -> Event t b -> Event t c
alignWithMaybe f ea eb =
  fmapMaybe (f <=< dmapToThese)
    $ merge
    $ DMap.fromList [LeftTag :=> ea, RightTag :=> eb]


--------------------------------------------------------------------------------
-- Accumulator
--------------------------------------------------------------------------------

-- | An 'Accumulator' type can be built by accumulating occurrences of an
-- 'Event'.
class HasTimeline t => Accumulator t f | f -> t where
  accum :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> a) -> a -> Event t b -> m (f a)
  accum f = accumMaybe $ \v o -> Just $ f v o
  accumM :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t a) -> a -> Event t b -> m (f a)
  accumM f = accumMaybeM $ \v o -> Just <$> f v o
  accumMaybe :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> Maybe a) -> a -> Event t b -> m (f a)
  accumMaybe f = accumMaybeM $ \v o -> return $ f v o
  accumMaybeM :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t (Maybe a)) -> a -> Event t b -> m (f a)
  mapAccum :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> (a, c)) -> a -> Event t b -> m (f a, Event t c)
  mapAccum f = mapAccumMaybe $ \v o -> bimap Just Just $ f v o
  mapAccumM :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t (a, c)) -> a -> Event t b -> m (f a, Event t c)
  mapAccumM f = mapAccumMaybeM $ \v o -> bimap Just Just <$> f v o
  mapAccumMaybe :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> (Maybe a, Maybe c)) -> a -> Event t b -> m (f a, Event t c)
  mapAccumMaybe f = mapAccumMaybeM $ \v o -> return $ f v o
  mapAccumMaybeM :: (MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t (Maybe a, Maybe c)) -> a -> Event t b -> m (f a, Event t c)

-- | Accumulate occurrences of an 'Event', producing an output occurrence each
-- time.  Discard the underlying 'Accumulator'.
mapAccum_ :: forall t m a b c. (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => (a -> b -> (a, c)) -> a -> Event t b -> m (Event t c)
mapAccum_ f z e = do
  (_ :: Behavior t a, result) <- mapAccum f z e
  return result

-- | Accumulate occurrences of an 'Event', possibly producing an output
-- occurrence each time.  Discard the underlying 'Accumulator'.
mapAccumMaybe_ :: forall t m a b c. (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => (a -> b -> (Maybe a, Maybe c)) -> a -> Event t b -> m (Event t c)
mapAccumMaybe_ f z e = do
  (_ :: Behavior t a, result) <- mapAccumMaybe f z e
  return result

-- | Accumulate occurrences of an 'Event', using a 'PushM' action and producing
-- an output occurrence each time.  Discard the underlying 'Accumulator'.
mapAccumM_ :: forall t m a b c. (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t (a, c)) -> a -> Event t b -> m (Event t c)
mapAccumM_ f z e = do
  (_ :: Behavior t a, result) <- mapAccumM f z e
  return result

-- | Accumulate occurrences of an 'Event', using a 'PushM' action and possibly
-- producing an output occurrence each time.  Discard the underlying
-- 'Accumulator'.
mapAccumMaybeM_ :: forall t m a b c. (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => (a -> b -> PushM t (Maybe a, Maybe c)) -> a -> Event t b -> m (Event t c)
mapAccumMaybeM_ f z e = do
  (_ :: Behavior t a, result) <- mapAccumMaybeM f z e
  return result

instance HasTimeline t => Accumulator t (Dynamic t) where
  accumMaybeM f z e = do
    rec let e' = flip push e $ \o -> do
              v <- sample $ current d'
              f v o
        d' <- holdDyn z e'
    return d'
  mapAccumMaybeM f z e = do
    rec let e' = flip push e $ \o -> do
              v <- sample $ current d'
              result <- f v o
              return $ case result of
                (Nothing, Nothing) -> Nothing
                _ -> Just result
        d' <- holdDyn z $ fmapMaybe fst e'
    return (d', fmapMaybe snd e')

instance HasTimeline t => Accumulator t (Behavior t) where
  accumMaybeM f z e = current <$> accumMaybeM f z e
  mapAccumMaybeM f z e = first current <$> mapAccumMaybeM f z e

instance HasTimeline t => Accumulator t (Event t) where
  accumMaybeM f z e = updated <$> accumMaybeM f z e
  mapAccumMaybeM f z e = first updated <$> mapAccumMaybeM f z e

-- | Create a new 'Event' by combining each occurence with the next value of the
-- list using the supplied function. If the list runs out of items, all
-- subsequent 'Event' occurrences will be ignored.
zipListWithEvent :: (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => (a -> b -> c) -> [a] -> Event t b -> m (Event t c)
zipListWithEvent f l e = do
  let f' a b = case a of
        h:t -> (Just t, Just $ f h b)
        _ -> (Nothing, Nothing) --TODO: Unsubscribe the event?
  mapAccumMaybe_ f' l e

-- | A 'Monad' that supports adjustment over time.  After an action has been
-- run, if the given events fire, it will adjust itself so that its net effect
-- is as though it had originally been run with the new value.  Note that there
-- is some issue here with persistent side-effects: obviously, IO (and some
-- other side-effects) cannot be undone, so it is up to the instance implementer
-- to determine what the best meaning for this class is in such cases.
class (HasTimeline t, Monad m) => MonadAdjust t m | m -> t where
  runWithReplace :: m a -> Event t (m b) -> m (a, Event t b)
  sequenceDMapWithAdjust :: GCompare k => DMap k m -> Event t (PatchDMap k m) -> m (DMap k Identity, Event t (PatchDMap k Identity))

instance (HasTimeline t, MonadAdjust t m) => MonadAdjust t (ReaderT r m) where
  runWithReplace a0 a' = do
    r <- ask
    lift $ runWithReplace (runReaderT a0 r) $ fmap (`runReaderT` r) a'
  sequenceDMapWithAdjust dm0 dm' = do
    r <- ask
    let loweredDm0 = DMap.map (`runReaderT` r) dm0
        loweredDm' = ffor dm' $ \(PatchDMap p) -> PatchDMap $
          DMap.map (\(ComposeMaybe mv) -> ComposeMaybe $ fmap (`runReaderT` r) mv) p
    lift $ sequenceDMapWithAdjust loweredDm0 loweredDm'

------------------
-- Cheap Functions
------------------

{-# INLINE pushAlwaysCheap #-}
pushAlwaysCheap :: HasTimeline t => (a -> PushM t b) -> Event t a -> Event t b
pushAlwaysCheap f = pushCheap (fmap Just . f)

{-# INLINE fmapMaybeCheap #-}
fmapMaybeCheap :: HasTimeline t => (a -> Maybe b) -> Event t a -> Event t b
fmapMaybeCheap f = pushCheap $ return . f

{-# INLINE fforMaybeCheap #-}
fforMaybeCheap :: HasTimeline t => Event t a -> (a -> Maybe b) -> Event t b
fforMaybeCheap = flip fmapMaybeCheap

{-# INLINE fforCheap #-}
fforCheap :: HasTimeline t => Event t a -> (a -> b) -> Event t b
fforCheap = flip fmapCheap

{-# INLINE fmapCheap #-}
fmapCheap :: HasTimeline t => (a -> b) -> Event t a -> Event t b
fmapCheap f = pushCheap $ return . Just . f

{-# INLINE tagCheap #-}
tagCheap :: HasTimeline t => Behavior t b -> Event t a -> Event t b
tagCheap b = pushAlwaysCheap $ \_ -> sample b

{-# INLINE mergeWithCheap #-}
mergeWithCheap :: HasTimeline t => (a -> a -> a) -> [Event t a] -> Event t a
mergeWithCheap = mergeWithCheap' id

{-# INLINE mergeWithCheap' #-}
mergeWithCheap' :: HasTimeline t => (a -> b) -> (b -> b -> b) -> [Event t a] -> Event t b
mergeWithCheap' f g es = fmapCheap (Prelude.foldl1 g . map (\(Const2 _ :=> Identity v) -> f v) . DMap.toList)
                       . merge
                       . DMap.fromDistinctAscList
                       . map (\(k, v) -> Const2 k :=> v)
                       $ zip [0 :: Int ..] es

--------------------------------------------------------------------------------
-- Deprecated functions
--------------------------------------------------------------------------------

-- | Create a new 'Event' that occurs if at least one of the supplied 'Event's
-- occurs. If both occur at the same time they are combined using 'mappend'.
{-# DEPRECATED appendEvents "If a 'Semigroup a' instance is available, use 'mappend'; otherwise, use 'alignWith (mergeThese mappend)' instead" #-}
appendEvents :: (HasTimeline t, Monoid a) => Event t a -> Event t a -> Event t a
appendEvents = alignWith $ mergeThese mappend

-- | Alias for 'headE'
{-# DEPRECATED onceE "Use 'headE' instead" #-}
onceE :: (HasTimeline t, MonadHold (Impl t) m, MonadFix m) => Event t a -> m (Event t a)
onceE = headE

-- | Run both sides of a 'These' monadically, combining the results.
{-# DEPRECATED sequenceThese "Use bisequenceA or bisequence from the bifunctors package instead" #-}
#ifdef USE_TEMPLATE_HASKELL
{-# ANN sequenceThese "HLint: ignore Use fmap" #-}
#endif
sequenceThese :: Monad m => These (m a) (m b) -> m (These a b)
sequenceThese t = case t of
  This ma -> fmap This ma
  These ma mb -> liftM2 These ma mb
  That mb -> fmap That mb
