# Reflex with Backpack

This package provides an implementation of Reflex specialized
to Spider using Backpack, demonstrating how Backpack can be built
on top of an existing, type-class based library without requiring
any source modifications.

## Building

* Have a GHC HEAD and cabal-install HEAD nightly installed.

* Make sure the submodules are checked out (`git submodule init && git
  submodule update`); we need unreleased versions of these packages
  because the released versions are not yet compatible with GHC HEAD.

* Run `cabal new-build -w /path/to/ghc-head`

## Architecture

There are a few ways we could go about Backpack'ing Reflex, and this
particular iteration has two goals:

1. Use the existing Reflex library without modification.  It should
   only be necessary to copy code when we want it to be specialized;
   any code which is not parametric over the Reflex backend should
   be reused from Reflex.

2. Remove the performance tax of having a Reflex typeclass.  All
   invocations of methods from Reflex should go directly to the
   actual implementation; we should be as fast as the "specialize
   Reflex to Spider" mode that the regular Reflex library can be
   run as.

The general idea is to replace the `Reflex` and `ReflexHost` type
classes with Backpack signatures representing them, `Reflex.Sig` and
`Reflex.Host.Sig` (respectively).  We have two internal libraries:
`indef`, which represents code that only depends on the `Reflex`
interface, and `host`, which represnets code that also depends on
`ReflexHost` (we split them because the `Pure` Reflex implementation
does not support `ReflexHost`.)

Let's take a side-by-side look at the `Reflex` type class,
and the corresponding `Reflex.Sig` signature:

```
-- Type class
class ( MonadHold t (PushM t)
      , MonadSample t (PullM t)
      , MonadFix (PushM t)
      , Functor (Dynamic t)
      , Applicative (Dynamic t)
      , Monad (Dynamic t)
      ) => Reflex t where
  data Behavior t :: * -> *
  data Event t :: * -> *
  data Dynamic t :: * -> *
  data Incremental t :: * -> *
  type PushM t :: * -> *
  type PullM t :: * -> *
  never :: Event t a
  ...

-- Signature
class HasTimeline t

data Impl t

type Event          t = C.Event         (Impl t)
type Dynamic        t = C.Dynamic       (Impl t)
type Behavior       t = C.Behavior      (Impl t)
type Incremental    t = C.Incremental   (Impl t)
type EventSelector  t = C.EventSelector (Impl t)
data PushM t a
data PullM t a

instance HasTimeline t => Functor       (Dynamic t)
instance HasTimeline t => Applicative   (Dynamic t)
instance HasTimeline t => Monad         (Dynamic t)
instance HasTimeline t => MonadSample   (Impl t) (PullM t)
instance HasTimeline t => MonadHold     (Impl t) (PushM t)
instance HasTimeline t => MonadSample   (Impl t) (PushM t)
instance HasTimeline t => MonadFix      (PushM t)
instance HasTimeline t => Monad         (PushM t)
instance HasTimeline t => Applicative   (PushM t)
instance HasTimeline t => Functor       (PushM t)
instance HasTimeline t => Monad         (PullM t)
instance HasTimeline t => Applicative   (PullM t)
instance HasTimeline t => Functor       (PullM t)

never :: HasTimeline t => Event t a
...
```

The `Reflex` type class is quite complicated, so let's step through
all of its features:

* First, `Reflex` is a type class over a type `t`.  Unusually,
  this type is usually instantiated with a type constructor
  applied to a type variable; for example, `Pure t` (different
  `t`, confusingly) or `SpiderTimeline x`.  In `Pure`, the type
  parameter identifies a moment in time (`Int` is a fairly common
  instantiation); `SpiderTimeline` is a phantom type parameter like the
  `s` in `ST s a` which is used to distinguish between distinct
  timelines (each running instance of Spider has a timeline that cannot
  be intermixed with other instances.)  In `Pure`, the `t` requires
  the instances `Enum t, HasTrie t, Ord t`; in `SpiderTimeline`, the `x`
  requires `HasSpiderTimeline`.

* `Reflex` has a number of associated data (`Behavior`,
  `Event`, `Dynamic` and `Incremental`), as well as two
  associated types (`PushM` and `PullM`).  These data and types
  are required to fulfill certain instances, listed in the superclasses
  of the instance.

* Finally, `Reflex` has a large number of methods that must be
  implemented by any Reflex engine.

We have a number of options for how to go about converting this into
Backpack, but in the end I went with the following scheme:

* First, we need a type to represent the main type parameter `t` of
  the `Reflex` class.  Originally, I picked a plain `data Timeline`
  to represent this, but unfortunately, this does not work with
  `SpiderTimeline`: if we have `pull :: PullM (SpiderTimeline x) a ->
  Behavior (SpiderTimeline x) a`, we can't rewrite this as `pull ::
  PullM a -> Behavior a`, as we've now lost the relationship between the
  phantom type parameters of `PullM` and `Behavior`.

  Thus, instead, we define a type constructor `data Impl t`, which
  takes as input the extra type parameter to let us pass along
  the phantom type variable.  We also need an abstract class
  `HasTimeline`, which will be used to record the extra constraints
  on the type variable.

  You might be wondering, why bother with `Impl` at all?  Inside
  the modules that import the signature, we are going to want
  to define instances like `instance HasTimeline t => Applicative (Behavior (Impl t))`
  If we don't have `Impl` here, the instances defined by the main
  library (`instance Reflex t => Applicative (Behavior t)`) will
  incoherently overlap; but we really want GHC to pick the *specialized*
  instances.

* Next, we need types for all of the associated data/types of `Reflex`.
  Here, I made an unusual design decision: for data families, rather
  than specify them as abstract data types in the signature, I instead
  refer *directly* to the data families from `Reflex.Class`.  The
  benefit of setting things up this way is that we can reuse
  any module from `reflex` which doesn't have a `Reflex` constraint
  but does rely on one of these associated types; if we make new
  abstract types, those modules have to be re-specialized (since
  we would not know that `Reflex.Class.Event` is the same as
  `Reflex.Sig.Event`).

  To avoid having to specify `Impl` everywhere, we define
  type signatures for these classes which insert the `Impl`
  application.

  I would have liked to do this trick for the type families as
  well, but it doesn't work: we need to specify instances
  for each of the superclasses of the `Reflex` class, but
  type synonym families are not allowed in instance heads.
  There might be some relaxation to GHC's rules here which would
  make this possible, but at the moment, it doesn't work.

  Note that we need to specify an instance for every superclass
  (this is how Backpack signatures behave), unlike superclasses
  which don't need to.

* Finally, we have the actual methods from the class, which are
  now top-level functions.  These are the functions that we
  are removing indirection for!
