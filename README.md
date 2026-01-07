# Graphplan in Lean

## Planning with Proof

This github repository contains the code for my paper on my [Graphplan](https://www.cs.cmu.edu/~avrim/Papers/graphplan.pdf) and [STRIPS](https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/strips.pdf) implementation in Lean.
Inspired by the [Python STRIPS implementation](https://github.com/tansey/strips).

## Planning

This repo has a standalone implementation of STRIPS in Lean that can be used as-is and has multiple functions to apply actions.
Because the primitive is a simple Lean type, this implementation is quite permissible in creating complicated STRIPS instances. See for example the `examples` folder, where, for testing purposes, the `Hano.lean` and `RocketN.lean` definitions are deppendant on the "difficulty" $n$ of the problem.

Additionally, there is a small operator, `>-` to make direct manipulation of the state easer to grasp, that is, a solution can be manually found by trying out to chain multiple actions. If an action is not applicable, the macro will fail and lean will show an error.
Taking the example from the [Wikipedia page of STRIPS](https://en.wikipedia.org/wiki/Stanford_Research_Institute_Problem_Solver), the following compiles and prints `true` (see `Graphplan.lean`):

```Lean
def Example_Simulation_End_state_DSL : STRIPS_Plan MonkeyBoxProp :=
  MonkeyBox_STRIPS_Plan -- The base plan
  >- Move A B
  >- MoveBox B C
  >- ClimbUp C
  >- TakeBananas C

#eval Search.is_valid_plan Example_Simulation_End_state_DSL [] -- true
```

## Solving

There are four implementations of solvers for STRIPS instances in this repository. Two breadth-first searches (see [below](#proof)), one best-first search (somewhat faster, breaks optimality guarantee) and Graphplan (significantly faster, better asymptotic runtime).

![Performance on the Rocket Problem with n pieces of cargo, in Milliseconds]("https://raw.githubusercontent.com/SeseMueller/graphplan/master/Latex%20Graphplan/Performance_on_RocketN.png")

## Proof

One of the major advantages of using Lean over other programming languages is the fact that lean can represent propositions and proofs of them. This is also used in the repository, as the second breadth-first search doesn't return just the list of actions to run in order to solve the problem, but also a proof that this list does, in fact solve the problem.

The proof is done statically, so one can know without having to run the code or check the return value, that the returned solution is correct.
