# replicator-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ReplicatorLean)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20478286.svg)](https://doi.org/10.5281/zenodo.20478286)

**replicator-lean: Formal Proofs for Replicator Dynamics on the Standard Simplex in Lean 4**

Lean 4 formal proofs for algebraic properties of replicator dynamics on the standard simplex. The development covers simplex invariance, fixed points, Nash equilibria, a Lyapunov identity for potential games, nonnegativity of fitness variance, and the algebraic core of the convergence criterion.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Replicator dynamics is a central model in evolutionary game theory. A population state `x` lies in the standard simplex when all strategy weights are nonnegative and sum to one. Given a fitness vector `f`, the replicator vector field is:

```text
xdot_i = x_i * (f_i - avgFitness x f)
```

where:

```text
avgFitness x f = sum_i x_i * f_i
```

This library machine-checks the basic algebra showing that the simplex mass is invariant, fixed points are exactly states where all supported strategies have average fitness, Nash equilibria are fixed points, and the potential-game Lyapunov derivative is the fitness variance.

## Setting

The formalisation works with vectors `Fin n -> Real`. The standard simplex predicate is:

```text
InSimplex x := (forall i, 0 <= x i) and sum_i x_i = 1
```

The fixed-point predicate states that every component of the replicator field vanishes:

```text
IsFixedPoint x f := forall i, replicatorField x f i = 0
```

The Nash equilibrium predicate used here states that `x` is in the simplex and no pure strategy earns more than the population average:

```text
IsNashEquilibrium x f := InSimplex x and forall j, f_j <= avgFitness x f
```

## Main result

The convergence module proves the algebraic core used in the potential-game convergence argument:

```text
(IsFixedPoint x f and forall j, f_j <= avgFitness x f)
  iff IsNashEquilibrium x f
```

The module documentation explains how this combines with the Lyapunov identity and LaSalle's invariance principle: in strict potential games, trajectories converge to the largest invariant subset where the fitness variance vanishes, which is the Nash equilibrium set.

## Project structure

```text
ReplicatorLean/
├── Defs.lean        — simplex membership, average fitness, replicator field,
│                      fixed points, Nash equilibria, fitness variance
├── Invariance.lean  — sum of vector-field components vanishes on the simplex
├── FixedPoints.lean — fixed-point characterisation and Nash implies fixed point
└── Convergence.lean — Lyapunov identity, variance nonnegativity,
                       variance-zero characterisation, convergence criterion
ReplicatorLean.lean  — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `simplex_invariant` | If `x` is in the simplex, then `sum_i replicatorField x f i = 0` |
| 2 | `replicator_fixed_point` | `IsFixedPoint x f` iff every supported strategy has fitness equal to `avgFitness x f` |
| 3 | `nash_is_fixed_point` | Every `IsNashEquilibrium x f` is an `IsFixedPoint x f` |
| 4 | `potential_game_lyapunov` | On the simplex, `sum_i f_i * replicatorField x f i = fitnessVariance x f` |
| 5 | `fitness_variance_nonneg` | On the simplex, `0 <= fitnessVariance x f` |
| 6 | `fitness_variance_eq_zero_iff` | On the simplex, `fitnessVariance x f = 0` iff `IsFixedPoint x f` |
| 7 | `replicator_convergence` | On the simplex, `(IsFixedPoint x f and forall j, f_j <= avgFitness x f)` iff `IsNashEquilibrium x f` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [lotka-volterra-lean](https://github.com/velvetmonkey/lotka-volterra-lean) — Lean 4 Lotka-Volterra dynamics
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [frank-wolfe-lean](https://github.com/velvetmonkey/frank-wolfe-lean) — Lean 4 Frank-Wolfe convergence
- [langevin-lean](https://github.com/velvetmonkey/langevin-lean) — Lean 4 bounded-noise Langevin convergence

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
