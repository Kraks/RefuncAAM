# Refunctionalization of Abstract Abstract Machines

This directory contains the artifact for the ICFP '18 submission "Refunctionalization of Abstract Abstract Machines (Functional Pearl)".

## Abstract

Abstracting abstract machines (AAM) is a systematic methodology for constructing abstract interpreters that are derived from concrete small-step abstract machines. Recent progress applies the same idea on definitional interpreters, and obtains big-step abstract definitional interpreters (ADI) written in monadic style. Yet, the relations between small-step abstracting abstract machines and big-step abstracting definitional interpreters are not well studied.

In this paper, we show their functional correspondence and how to syntactically transform small-step abstract abstract machines into big-step abstract definitional interpreters. The transformations include linearization, fusing, disentangling, refunctionalizing, and un-CPS to direct-style with delimited controls. Linearization expresses non-deterministic choices by first-order data types, after which refunctionalization sequentializes the evaluation order by higher-order functions. All transformations properly handle the collecting semantics and the nondeterminism of abstract interpretation.

Following the idea that in deterministic languages, evaluation contexts of reduction semantics are defunctionalized continuations, we further show that in nondeterministic languages, evaluation contexts are refunctionalized to extended continuations style. Remarkably, we reveal how precise call/return matching in control-flow analysis is obtained by refunctionalizing a small-step abstract abstract machine with proper caching.

## Getting Started

### To compile
```
  sbt compile
```

### To test
```
  sbt test
```

## Contents

![Transformation diagram](images/transformations.png)

### Relations to the Paper

### Tests
