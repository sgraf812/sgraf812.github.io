---
title: All About Strictness Analysis (part 1)
tags: haskell strictness analysis
---

Non-strict languages like Haskell often require the programmer to reason about strictness to achieve good performance.
A while ago, Michael Snoyman wrote a [blog post](https://www.fpcomplete.com/blog/2017/09/all-about-strictness) about this, giving an introduction on the matter as well as an overview over the tools at our disposal.

In this post, I want to offer another, more surgical approach to plugging space leaks that works hand in hand with optimizations carried out by the compiler.

<!--more-->

## The Setting

Michael Snoyman fixed problems due to laziness by making ample use of strictness annotations.
This is the right approach when you run into space leaks in debug builds.
It’s also good practice for library writers, where you cannot anticipate usage patterns, so the least you could do is force strict parameters as early as possible.

Running example in Snoyman’s blog post were variants of the following program computing the average of a list of `Int`egers:

```haskell
data RunningTotal = RunningTotal
  { sum   :: Int
  , count :: Int
  }

printAverage :: RunningTotal -> IO ()
printAverage (RunningTotal sum count)
  | count == 0 = error "Need at least one value!"
  | otherwise = print (fromIntegral sum / fromIntegral count :: Double)

printListAverage :: [Int] -> IO ()
printListAverage = go (RunningTotal 0 0)
  where
    go rt [] = printAverage rt
    go (RunningTotal sum count) (x:xs) =
      go (RunningTotal (sum + x) (count + 1)) xs

main :: IO ()
main = printListAverage [1..1000000]
```

In absence of any optimization, this is quite hungry for memory:

```sh
$ stack --resolver=nightly-2017-12-01 ghc -- -O0 average.hs && ./average +RTS -s
500000.5
     258,650,856 bytes allocated in the heap
     348,098,952 bytes copied during GC
      74,388,992 bytes maximum residency (9 sample(s))
         599,832 bytes maximum slop
             179 MB total memory in use (0 MB lost due to fragmentation)
```

Significant numbers are roughly 250MB in allocations over the course of execution, as well as a maximum working set of 74MB.
I’m currently on stackage `nightly-2017-12-01` (GHC 8.2.2) on a Windows box, which might explain differences in measurement.

The post goes on to annotate the accumulating parameter of `go` with bang patterns:

```haskell
{-# LANGUAGE BangPatterns #-}

data RunningTotal = RunningTotal
  { sum   :: Int
  , count :: Int
  }

printAverage :: RunningTotal -> IO ()
printAverage (RunningTotal sum count)
  | count == 0 = error "Need at least one value!"
  | otherwise = print (fromIntegral sum / fromIntegral count :: Double)

printListAverage :: [Int] -> IO ()
printListAverage = go (RunningTotal 0 0)
  where
    go rt [] = printAverage rt
    go (RunningTotal !sum !count) (x:xs) = -- only this line changed
      go (RunningTotal (sum + x) (count + 1)) xs

main :: IO ()
main = printListAverage [1..1000000]
```

This has a great effect on maximum residency:

```sh
$ stack --resolver=nightly-2017-12-01 ghc -- -O0 average.hs && ./average +RTS -s
500000.5
     192,099,048 bytes allocated in the heap
         245,416 bytes copied during GC
          42,856 bytes maximum residency (2 sample(s))
          30,872 bytes maximum slop
               2 MB total memory in use (0 MB lost due to fragmentation)
...
INIT    time    0.000s  (  0.000s elapsed)
MUT     time    0.031s  (  0.029s elapsed)
GC      time    0.000s  (  0.001s elapsed)
EXIT    time    0.000s  (  0.000s elapsed)
Total   time    0.031s  (  0.030s elapsed)
```

The program now executes in constant residency, which, in the presence of garbage collection, guarantees constant space usage! Nonetheless, we still produce a lot of garbage (190MB) and need 30ms to arrive at that result.

## Optimizations

Compare that to what happens when we compile with optimizations on:

```sh
$ stack --resolver=nightly-2017-12-01 ghc -- -O2 average.hs && ./average +RTS -s
500000.5
     128,098,744 bytes allocated in the heap
          13,800 bytes copied during GC
          42,856 bytes maximum residency (1 sample(s))
          30,872 bytes maximum slop
               2 MB total memory in use (0 MB lost due to fragmentation)
...
INIT    time    0.000s  (  0.000s elapsed)
MUT     time    0.016s  (  0.014s elapsed)
GC      time    0.000s  (  0.000s elapsed)
EXIT    time    0.000s  (  0.000s elapsed)
Total   time    0.016s  (  0.015s elapsed)
```

Optimizations chipped off a huge amount of total allocations and also cut execution time in half.

How can we improve on this? By deleting the two bangs we inserted earlier (simply for dramatic effect) and placing one in the pattern of `printAverage` instead:

```haskell
{-# LANGUAGE BangPatterns #-}

data RunningTotal = RunningTotal
  { sum   :: Int
  , count :: Int
  }

printAverage :: RunningTotal -> IO ()
printAverage (RunningTotal !sum count) -- New bang here
  | count == 0 = error "Need at least one value!"
  | otherwise = print (fromIntegral sum / fromIntegral count :: Double)

printListAverage :: [Int] -> IO ()
printListAverage = go (RunningTotal 0 0)
  where
    go rt [] = printAverage rt
    go (RunningTotal sum count) (x:xs) = -- No more bangs here
      go (RunningTotal (sum + x) (count + 1)) xs

main :: IO ()
main = printListAverage [1..1000000]
```

Compile and execute this in old fashion with optimizations on:

```sh
$ stack --resolver=nightly-2017-12-01 ghc -- -O2 average.hs && ./average +RTS -s
500000.5
      80,098,744 bytes allocated in the heap
           5,864 bytes copied during GC
          42,856 bytes maximum residency (1 sample(s))
          30,872 bytes maximum slop
               2 MB total memory in use (0 MB lost due to fragmentation)
...
INIT    time    0.000s  (  0.000s elapsed)
MUT     time    0.000s  (  0.009s elapsed)
GC      time    0.000s  (  0.000s elapsed)
EXIT    time    0.000s  (  0.000s elapsed)
Total   time    0.000s  (  0.009s elapsed)
```

Another huge chunk of allocations is gone and execution time reduced by at least 30% again! What just happened?

## The compiler can reason about strictness

The strictness analysis of GHC (which is integrated in its [Demand Analyzer](https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/Demand), a behemoth that interleaves three different analyses) is quite capable.
Without any intervention it would have recognized that the recursive `go` is strict not only in the `RunningTotal` constructor, but also in its `count` field.
Perhaps surprisingly, it would find the `sum` field *not* to be evaluated strictly.

That’s due to a subtlety in the definition of `printAverage`:
Note that in the `count == 0` error case that `sum` isn’t evaluated at all!
And indeed, `printAverage (RunningTotal undefined 0)` will print the expected error message instead of crashing due to `undefined`, which is the very definition of being lazy in `sum`.
This extends to a call like `go (RunningTotal undefined 0) []`, so GHC can't just unbox the `sum` field even if the recursive case of `go` is annotated.
So placing a bang in `printAverage` makes sense after all: 
There isn't much utility in allowing calls like `printAverage (RunningTotal undefined 0)`.

What I found quite essential to pin down the cause of this performance regression is a combination of looking at the GHC Core output as well as reproduce what strictness analysis found out.
Let’s start with a crash course on a simple strictness analysis similar to GHC’s.

In order to be scalable, GHC summarizes each function by a *demand signature* (consult the [GHC wiki page](https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/Demand) for details), part of which relates how a single call evaluates its arguments and free variables.
The signature for `printAverage` for example looks like `<S(LS(S)),_>` (we elide usage demands, suggested by the `_` wildcard), which reads as:
When `printAverage` is called with one argument, it will evaluate that argument strictly (the `RunningTotal` box), as well as unpack the boxed `Int` in its second field (`count`) strictly, while being `L`azy in the first field (`sum`).

It’s not hard to see how to arrive at that signature:
We (and the compiler) assume a call with one argument (ignoring intricacies regarding `IO`), and see that the first branch is lazy in `sum`, while the second is strict in both.
Prior to that, the `RunningTotal` is unpacked (evaluated!) and `count` is compared to 0, which also entails unpacking the `Int` constructor to get at the unboxed `Int#`.
Combined, `RunningTotal`s `count` field is put under strictness `S(S)` (the unpacked `Int#` in the box is evaluated strictly), while `sum` is put under strictness `L`, resulting in said strictness demand of `S(LS(S))` on the `RunningTotal` argument.

Non-recursive functions are trivial to analyze and are inlined most of the time anyway.
What about a recursive function, such as `go`?
Let’s see what GHC found out by dumping the module’s Core IR after the strictness analyzer has been run with `-ddump-stranal` (simplified):

```haskell
$ stack --resolver=nightly-2017-12-01 ghc -- -O2 average.hs -ddump-stranal -fforce-recomp
[1 of 1] Compiling Main             ( average.hs, average.o )

==================== Demand analysis ====================
...
go :: RunningTotal -> [Int] -> IO ()
[...
 Arity=2,
 Str=<S(LS(S)),1*U(1*U(U),1*U(U))><S,1*U>,
 ...]
go
  = \ (rt :: RunningTotal)
      (xs :: [Int]) ->
      case xs of
        [] -> -- inlining of `printAverage rt`
        : x xs ->
          case rt of
            RunningTotal sum count ->
              go
                (Main.RunningTotal
                  (GHC.Num.$fNumInt_$c+ sum x)
                  (case count of
                    GHC.Types.I# count# ->
                      GHC.Types.I# (GHC.Prim.+# count# 1#)))
                xs
...
==================== Demand analysis ====================
...
```

Note that there are multiple runs of the demand analyzer, but we’ll focus on the first run for now, before any of the strictness information was exploited by transformations downstream.

Crucial is the demand signature assigned to `go`, which is available as the `Str` attribute (usage demands elided again): `<S(LS(S)),_><S,_>`.
This is just as expected.
The first `RunningTotal` argument is unpacked all the time (in the `[]` case, that’s done by `printAverage`), but its `sum` field is only evaluated lazily because the error case in `printAverage` isn’t strict in it, so by induction, `go` is neither.
The second argument is the list of integers to average, which we immediately match on, so naturally its outer constructor is used strictly.

It’s one thing for humans to reason like this, but how do we teach this to a compiler?
The key here is inductive reasoning: Under the assumption that `go` has the above demand signature to be unleashed at recursive call sites, we can indeed verify `go` has this signature.

For that, the compiler initially assumes the most *optimistic* demand signature possible for `go`, which corresponds to `<S(S(S)S(S)),_><S,_>`<sup id="a1"><a href="#f1">1</a></sup>, the demand a `deepseq` would put on the arguments.
Assuming this for the recursive case, we can see that the newly constructed `RunningTotal (sum + x) (count + 1)` is `deepseq`ed immediately, which translates into a strictness of `S(S)` on both fields of the `RunningTotal` argument.

In the base case, however, the call to `printAverage` causes the `count` field to only be evaluated lazily.
That’s enough for the whole case match to be lazy in `count`, so the computed strictness signature is `<S(LS(S)),_><S,_>`.
Now the compiler has to reiterate analysis of `go`, because the assumed signature was too optimistic.
Fortunately, under the assumption of `<S(LS(S)),_><S,_>` for the recursive call, we arrive at exactly the same signature.
Analysis has reached a *fixed-point* in its endeavour to find a conservative approximation for the strictness properties of `go` at runtime.

## All boxes must go

Having a basic understanding of how strictness analysis works, we see that `printAverage` is the reason why `sum` isn’t unboxed.
As soon as we add the bang in the relevant position, as I foreshadowed above, we arrive at the following, simplified Core output:

```haskell
$ stack --resolver=nightly-2017-12-01 ghc -- -O2 average.hs -ddump-simpl -fforce-recomp
...
Main.main_$s$wgo
  :: [Int] -> GHC.Prim.Int# -> GHC.Prim.Int# -> IO ()
[GblId, Arity=3, Str=<S,1*U><S,U><L,U>]
Main.main_$s$wgo
  = \ (xs :: [Int])
      (count :: GHC.Prim.Int#)
      (sum :: GHC.Prim.Int#) ->
      case xs of
        [] ->
          case count of
            0# -> lvl2_r4lk -- error "..."
            _ ->
              (GHC.IO.Handle.Text.hPutStr2
                 GHC.IO.Handle.FD.stdout
                 (case GHC.Prim./##
                         (GHC.Prim.int2Double# sum) (GHC.Prim.int2Double# wild1_X1r)
                  of
                    _ ->
                      GHC.Float.$w$sshowSignedFloat
                        GHC.Float.$fShowDouble2
                        GHC.Float.minExpt
                        wild4_a3Qb
                        (GHC.Types.[] @ Char))
                 GHC.Types.True)
        : x xs ->
          $wgo_r4ll
            (case x of
              GHC.Types.I# y ->
                GHC.Types.I# (GHC.Prim.+# sum y))
            (GHC.Prim.+# count 1#)
            xs
...
```

Note that the `RunningTotal` box is completely gone.
That’s due to GHC optimizing away repeated boxing and unboxing in its [worker/wrapper transformation](http://www.cs.nott.ac.uk/~pszgmh/wrapper-extended.pdf), which is the pass that profits most significantly from strictness information. Without strictness analysis, no unboxing happens, even if you annotate bindings with bangs or activate `-XStrict`.

All 80MB of remaining allocation (we measured this above) are due to the list of integers.
We can do better by recognizing the fold pattern in `go` and make use of `foldl` (that’s right, the lazy one!), which takes part in list fusion since GHC 7.10:

```haskell
{-# LANGUAGE BangPatterns #-}

data RunningTotal = RunningTotal
  { sum   :: Int
  , count :: Int
  }

printAverage :: RunningTotal -> IO ()
printAverage (RunningTotal !sum count)
  | count == 0 = error "Need at least one value!"
  | otherwise = print (fromIntegral sum / fromIntegral count :: Double)

printListAverage :: [Int] -> IO ()
printListAverage = printAverage . foldl f (RunningTotal 0 0)
  where
    f (RunningTotal sum count) x = RunningTotal (sum + x) (count + 1)
    
main :: IO ()
main = printListAverage [1..1000000]
```

```sh
$ stack --resolver=nightly-2017-12-01 ghc -- -O2 average.hs && ./average +RTS -s
500000.5
          98,784 bytes allocated in the heap
           1,752 bytes copied during GC
          42,856 bytes maximum residency (1 sample(s))
          26,776 bytes maximum slop
               2 MB total memory in use (0 MB lost due to fragmentation)
...
INIT    time    0.000s  (  0.000s elapsed)
MUT     time    0.000s  (  0.002s elapsed)
GC      time    0.000s  (  0.000s elapsed)
EXIT    time    0.000s  (  0.000s elapsed)
Total   time    0.000s  (  0.003s elapsed)
```

That’s only 3ms (from 9ms earlier), and allocations have completely vanished! Let’s look at the Core output:

```haskell
Main.main_$s$wgo [Occ=LoopBreaker]
  :: GHC.Prim.Int# -> GHC.Prim.Int# -> GHC.Prim.Int# -> RunningTotal
[GblId, Arity=3, Caf=NoCafRefs, Str=<L,U><L,U><S,1*U>m]
Main.main_$s$wgo
  = \ (sc_s4sk :: GHC.Prim.Int#)
      (sc1_s4sj :: GHC.Prim.Int#)
      (sc2_s4si :: GHC.Prim.Int#) ->
      case sc2_s4si of wild_X1h {
        __DEFAULT ->
          Main.main_$s$wgo
            (GHC.Prim.+# sc_s4sk 1#)
            (GHC.Prim.+# sc1_s4sj wild_X1h)
            (GHC.Prim.+# wild_X1h 1#);
        1000000# ->
          Main.RunningTotal
            (GHC.Types.I# (GHC.Prim.+# sc1_s4sj 1000000#))
            (GHC.Types.I# (GHC.Prim.+# sc_s4sk 1#))
      }
```

Amazing! No boxing happening at all.
That should be enough to reach C level performance, given a good compiler backend.
The takeaway is that using `foldl` is great as long as list fusion kicks in.

## Summary
This post tried to demonstrate how to debug strictness in the face of compiler optimizations to achieve minimal time and space footprints.
For that, we re-enacted how the compiler analyzes strictness properties of functions, to eventually pin down the subtle culprit in `printAverage`.
This kind of debugging is only possible through having a rough idea of strictness analysis and reading relevant GHC Core fragments and as such only makes sense with optimizations activated.

Of course, library writers have good reason to sprinkle bang patterns more liberally:
They need to guarantee that the maximum residency stays as low as possible for snappy `-O0` performance.
That’s what experimentally placing bang patterns at accumulators is good for:
Keeping the maximum residency at a minimum, so that time spent on GC is as low as possible.
It’s *not* good for teaching GHC what to unbox (e.g. reducing total allocations by more than a constant factor), as that doesn’t happen anyway at `-O0`.
And as soon as optimizations kick in, strictness analysis is mostly smart enough to figure things out by itself.

The next part of this series will implement a strictness analysis with the help of [`datafix`](https://github.com/sgraf812/datafix), a new library of mine for writing static analyses.

Finally, some links for further reading:

- [Edward Yang: Anatomy of a thunk leak (2011)](http://blog.ezyang.com/2011/05/anatomy-of-a-thunk-leak/)
- [Don Steart: Write Haskell as fast as C (2008)](https://donsbot.wordpress.com/2008/05/06/write-haskell-as-fast-as-c-exploiting-strictness-laziness-and-recursion/)
- [Haskell Wiki on Strictness (Analysis)](https://wiki.haskell.org/Performance/Strictness#Strictness_analysis)

<b id="f1">1</b> That’s actually a bit simplified, as the real signature is `<B,_><B,_>`, where `B` denotes a *hyperstrict* demand as explained on [the wiki page](https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/Demand). <a href="#a1">↩</a>