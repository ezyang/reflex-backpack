{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
-- | This module is the implementation of the 'Spider' 'Reflex' engine.  It uses
-- a graph traversal algorithm to propagate 'Event's and 'Behavior's.
module Reflex.Spider.Backpack (
    module Reflex.Spider.Backpack,
    R.Reflex, Event, Dynamic, Behavior, Incremental,
    EventSelector(..), MonadHold(..), MonadSample(..)
) where

import Control.Applicative
import Control.Monad hiding (forM, forM_, mapM, mapM_, sequence)
import Control.Monad.Identity hiding (forM, forM_, mapM, mapM_, sequence)
import Control.Monad.Reader hiding (forM, forM_, mapM, mapM_, sequence)
import Data.Coerce
import Data.Function
import Data.Dependent.Map (DMap, DSum (..))
import Data.GADT.Compare
import Data.Maybe
import GHC.IORef (IORef (..))
import Unsafe.Coerce

#ifdef DEBUG_CYCLES
import Control.Monad.State hiding (forM, forM_, mapM, mapM_, sequence)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid (mempty)
import Data.Tree (Forest, Tree (..), drawForest)
#endif

import Data.Type.Coercion
import Reflex.Class hiding (Reflex(..))
import Reflex.Class (Behavior, Event, Dynamic, Incremental)
import qualified Reflex.Class as R
import qualified Reflex.Host.Class as H

import Reflex.Spider.Internal hiding (push, merge, coincidence, switch, fan, select, EventSelector, pull, pushCheap, Dynamic, Behavior, Event)
import qualified Reflex.Spider.Internal as I

-- Note: must come last to silence warnings due to AMP on GHC < 7.10
import Prelude hiding (any, concat, mapM, mapM_, sequence)

#ifdef DEBUG_TRACE_EVENTS
import System.IO (stderr)
import qualified Data.ByteString.Char8 as BS8
#endif

type PullM = SpiderPullM
type PushM = SpiderPushM

type Impl = SpiderTimeline
type HasTimeline = HasSpiderTimeline

{-# INLINABLE never #-}
never :: HasTimeline t => Event (Impl t) a
never = SpiderEvent eventNever

{-# INLINABLE constant #-}
constant :: HasTimeline t => a -> Behavior (Impl t) a
constant = SpiderBehavior . behaviorConst

{-# INLINE push #-}
push :: HasTimeline t => (a -> PushM t (Maybe b)) -> Event (Impl t) a -> Event (Impl t) b
push f = SpiderEvent . I.push (coerce f) . unSpiderEvent

{-# INLINE pushCheap #-}
pushCheap :: HasTimeline t => (a -> PushM t (Maybe b)) -> Event (Impl t) a -> Event (Impl t) b
pushCheap f = SpiderEvent . I.pushCheap (coerce f) . unSpiderEvent

{-# INLINABLE pull #-}
pull :: HasTimeline t => PullM t a -> Behavior (Impl t) a
pull = SpiderBehavior . I.pull . coerce

{-# INLINABLE merge #-}
merge :: HasTimeline t => GCompare k => DMap k (Event (Impl t)) -> Event (Impl t) (DMap k Identity)
merge = SpiderEvent . I.merge . dynamicConst . (coerce :: DMap k (R.Event (SpiderTimeline x)) -> DMap k (I.Event x))

{-# INLINABLE fan #-}
fan :: (HasTimeline t, GCompare k) => Event (Impl t) (DMap k Identity) -> EventSelector (Impl t) k
fan e = R.EventSelector $ SpiderEvent . I.select (I.fan (unSpiderEvent e))

{-# INLINABLE switch #-}
switch :: HasTimeline t => Behavior (Impl t) (Event (Impl t) a) -> Event (Impl t) a
switch = SpiderEvent . I.switch . (coerce :: I.Behavior x (R.Event (SpiderTimeline x) a) -> I.Behavior x (I.Event x a)) . unSpiderBehavior

{-# INLINABLE coincidence #-}
coincidence :: HasTimeline t => Event (Impl t) (Event (Impl t) a) -> Event (Impl t) a
coincidence = SpiderEvent . I.coincidence . (coerce :: I.Event x (R.Event (SpiderTimeline x) a) -> I.Event x (I.Event x a)) . unSpiderEvent

{-# INLINABLE current #-}
current :: HasTimeline t => Dynamic (Impl t) a -> Behavior (Impl t) a
current = SpiderBehavior . dynamicCurrent . unSpiderDynamic

{-# INLINABLE updated #-}
updated :: HasTimeline t => Dynamic (Impl t) a -> Event (Impl t) a
updated = coerce $ SpiderEvent . dynamicUpdated . unSpiderDynamic

{-# INLINABLE unsafeBuildDynamic #-}
unsafeBuildDynamic :: HasTimeline t => PullM t a -> Event (Impl t) a -> Dynamic (Impl t) a
unsafeBuildDynamic readV0 v' = SpiderDynamic $ dynamicDynIdentity $ unsafeDyn (coerce readV0) $ coerce $ unSpiderEvent v'

{-# INLINABLE unsafeBuildIncremental #-}
unsafeBuildIncremental :: (HasTimeline t, Patch p) => PullM t (PatchTarget p) -> Event (Impl t) p -> Incremental (Impl t) p
unsafeBuildIncremental readV0 dv = SpiderIncremental $ dynamicDyn $ unsafeDyn (coerce readV0) $ unSpiderEvent dv

{-# INLINABLE mergeIncremental #-}
mergeIncremental :: (HasTimeline t, GCompare k) => Incremental (Impl t) (PatchDMap k (Event (Impl t))) -> Event (Impl t) (DMap k Identity)
mergeIncremental = SpiderEvent . I.merge . (unsafeCoerce :: I.Dynamic x (PatchDMap k (R.Event (SpiderTimeline x))) -> I.Dynamic x (PatchDMap k (I.Event x))) . unSpiderIncremental

{-# INLINABLE currentIncremental #-}
currentIncremental :: (HasTimeline t, Patch p) => Incremental (Impl t) p -> Behavior (Impl t) (PatchTarget p)
currentIncremental = SpiderBehavior . dynamicCurrent . unSpiderIncremental

{-# INLINABLE updatedIncremental #-}
updatedIncremental :: (HasTimeline t, Patch p) => Incremental (Impl t) p -> Event (Impl t) p
updatedIncremental = SpiderEvent . dynamicUpdated . unSpiderIncremental

{-# INLINABLE incrementalToDynamic #-}
incrementalToDynamic :: (HasTimeline t, Patch p) => Incremental (Impl t) p -> Dynamic (Impl t) (PatchTarget p)
incrementalToDynamic (SpiderIncremental i) = SpiderDynamic $ dynamicDynIdentity $ unsafeDyn (readBehaviorUntracked $ dynamicCurrent i) $ flip I.push (dynamicUpdated i) $ \p -> do
  c <- readBehaviorUntracked $ dynamicCurrent i
  return $ Identity <$> apply p c --TODO: Avoid the redundant 'apply'

eventCoercion :: HasTimeline t => Coercion a b -> Coercion (Event (Impl t) a) (Event (Impl t) b)
eventCoercion Coercion = Coercion

behaviorCoercion :: HasTimeline t => Coercion a b -> Coercion (Behavior (Impl t) a) (Behavior (Impl t) b)
behaviorCoercion Coercion = Coercion

dynamicCoercion :: HasTimeline t => Coercion a b -> Coercion (Dynamic (Impl t) a) (Dynamic (Impl t) b)
dynamicCoercion = unsafeCoerce --TODO: How can we avoid this unsafeCoerce?  This is safe only because we know how Identity works as a Patch instance

type EventTrigger = RootTrigger
type EventHandle = SpiderEventHandle
type HostFrame = SpiderHostFrame

subscribeEventHostFrame
    :: HasTimeline t
    => Event (Impl t) a -> HostFrame t (EventHandle t a)
subscribeEventHostFrame = H.subscribeEvent

newEventWithTriggerHostFrame
    :: HasTimeline t
    => (EventTrigger t a -> IO (IO ())) -> HostFrame t (Event (Impl t) a)
newEventWithTriggerHostFrame = H.newEventWithTrigger

newFanEventWithTriggerHostFrame
    :: (HasTimeline t, GCompare k)
    => (forall a. k a -> EventTrigger t a -> IO (IO ())) -> HostFrame t (EventSelector (Impl t) k)
newFanEventWithTriggerHostFrame = H.newFanEventWithTrigger
