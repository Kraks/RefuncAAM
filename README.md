# Refunctionalization of Abstract Abstract Machines

This directory contains the artifact for the ICFP '18 submission "Refunctionalization of Abstract Abstract Machines (Functional Pearl)".

## Abstract

Abstracting abstract machines (AAM) is a systematic methodology for constructing abstract interpreters that are derived from concrete small-step abstract machines. Recent progress applies the same idea on definitional interpreters, and obtains big-step abstract definitional interpreters (ADI) written in monadic style. Yet, the relations between small-step abstracting abstract machines and big-step abstracting definitional interpreters are not well studied.

In this paper, we show their functional correspondence and how to syntactically transform small-step abstract abstract machines into big-step abstract definitional interpreters. The transformations include linearization, fusing, disentangling, refunctionalizing, and un-CPS to direct-style with delimited controls. Linearization expresses non-deterministic choices by first-order data types, after which refunctionalization sequentializes the evaluation order by higher-order functions. All transformations properly handle the collecting semantics and the nondeterminism of abstract interpretation.

Following the idea that in deterministic languages, evaluation contexts of reduction semantics are defunctionalized continuations, we further show that in nondeterministic languages, evaluation contexts are refunctionalized to extended continuations style. Remarkably, we reveal how precise call/return matching in control-flow analysis is obtained by refunctionalizing a small-step abstract abstract machine with proper caching.

## Getting Started

You should have Oracle JDK (>= 8) and `sbt` (>= 0.13) installed. Other dependencies of Scala and libraries are specified in `build.sbt`.

### To compile
```
  sbt compile
```

### To test
```
  sbt test
```

### To generate the paper
```
  cd paper
  make
```

## Step-by-Step Instructions

### Relations to the Paper

![Transformation diagram](images/transformations.png)

This artifact contains Scala implementations that correspond to semantic artifacts in the above transformation diagram.

#### Section 2.1

The abstract syntax are specified in file `src/main/scala/refunc/ast/Expr.scala`. For convenience of testing, we implement an extended abstract syntax in ANF comparing with the one described in the paper: 1) Integers as atomic expressions are supported. 2) To create recursive bindings, the users may use `letrec`.

#### Section 2.2

In the transformation diagram, the starting point at the bottom left corner is concrete _abstract machines_. `src/main/scala/refunc/CESK.scala` contains a concrete CESK machine implementation (object `CESK`), and also a refunctionalized definitional interpreter in continuation-passing style (object `RefuncCESK`).

#### Section 2.3

A standard _abstract abstract machine (AAM)_ is implemented object `SmallStep` in `src/main/scala/refunc/SmallStep.scala`. The basic code structures shared by the rest abstract machines and abstract interpreters are contained in `src/main/scala/refunc/ANFAAMBasis.scala`.

#### Section 2.4

We implement a variant of abstract abstract machines -- AAM with unbounded stack in `src/main/scala/refunc/SmallStepUB.scala`. This artifact forms the beginning of transformations shown in the paper.

#### Section 3

The linearized AAM with unbounded stack (UB) is implemented in `src/main/scala/refunc/LinearSmallStepUBStack.scala`.

#### Section 4

By applying fusing transformation on the linearized AAM with UB, we show the fused AAM in `src/main/scala/refunc/FusedLinearSmallStepUBStack.scala`.

#### Section 5

The disentangled AAM is implemented in `src/main/scala/refunc/DisentangledLinearSmallStepUBStack.scala`, which identifies the first-order data type representing continuations in the abstract abstract machines. 

#### Section 6

The implementation of refunctionalized AAM is object `RefuncCPS` in `src/main/scala/refunc/RefuncCPS.scala`. In the paper, we also show a simplified version withou caching, which is implemented in `src/main/scala/refunc/RefuncCPSNoCache.scala`.

Additionally, as a reference of sound pushdown control-flow analysis, AAM with P4F allocator is implemented in `src/main/scala/refunc/SmallStepP4F.scala`. We use this to further test the pushdown control-flow property of our refunctionalized AAM.

#### Section 7

By representing the extended continuation-passing style with delimited control operators, we implement a direct-style abstract interpreter in object `DirectStyleDC` of file `src/main/scala/refunc/DirectStyle.scala`.

As we mentioned in Section 7, direct-style abstract interpreter using side effects and `for` comprehension is also feasible. We show this experimental implementation in object `DirectStyleSideEff` (also in file `DirectStyle.scala`).

### Tests

To concretely establish the correspondences, we provide a set of programs and test the equivalence of analyzed results from every abstract interpreters in our transformations. For details of testing criteria, see `src/test/scala/refunc/Test.scala`.
