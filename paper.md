# replicator-lean: Formal Proofs for Replicator Dynamics on the Standard Simplex in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`replicator-lean` is a Lean 4 / Mathlib library formalising core algebraic facts about replicator dynamics on the standard simplex. The library defines simplex membership, average fitness, the replicator vector field, fixed points, Nash equilibria, and fitness variance for vectors indexed by `Fin n`. It proves simplex mass invariance, the fixed-point characterisation, Nash equilibria as fixed points, the potential-game Lyapunov identity, non-negativity and zero-characterisation of variance, and the algebraic convergence criterion relating fixed points and Nash equilibria. The development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Replicator dynamics is a standard model in evolutionary game theory. A population state assigns a non-negative weight to each strategy, and the weights sum to one. Strategies whose fitness exceeds the population average grow; strategies below average shrink. This mechanism is captured by the vector field

```text
xdot_i = x_i * (f_i - avgFitness x f).
```

The first algebraic facts about this vector field are fundamental. The sum of the components is zero on the simplex, so total population mass is invariant. A state is a fixed point precisely when all strategies in its support have average fitness. Nash equilibria, in the sense used in the library, are fixed points. In potential games, the derivative of the potential along the vector field is the fitness variance, which is non-negative and vanishes exactly at fixed points.

`replicator-lean` formalises these identities over finite strategy sets `Fin n`. It does not formalise existence and uniqueness of ODE solutions or a full LaSalle invariance theorem for trajectories. Instead, it supplies the algebraic proof components that such a trajectory-level theorem would use.

## 2. Library Overview

The project is organised into four implementation modules plus a root import file:

- `ReplicatorLean/Defs.lean` defines the standard simplex predicate, average fitness, the replicator vector field, fixed points, Nash equilibria, and fitness variance.
- `ReplicatorLean/Invariance.lean` proves the simplex mass-invariance identity.
- `ReplicatorLean/FixedPoints.lean` proves the fixed-point characterisation and that Nash equilibria are fixed points.
- `ReplicatorLean/Convergence.lean` proves the Lyapunov identity, variance non-negativity, the zero-variance fixed-point characterisation, and the algebraic convergence criterion.
- `ReplicatorLean.lean` is the root module importing the library.

The project depends on:

- Lean `v4.28.0`
- Mathlib `v4.28.0`

The formal development contains zero `sorry`, zero `admit`, and introduces no project-specific axioms. It is written against Lean 4 and Mathlib, using standard Lean/Mathlib axioms only.

The formal setting uses finite real vectors:

```lean
variable {n : Nat}
x f : Fin n -> Real
```

The standard simplex is defined by

```lean
def InSimplex (x : Fin n -> Real) : Prop :=
  (forall i, 0 <= x i) and sum_i x_i = 1.
```

The average fitness and vector field are

```text
avgFitness x f = sum_i x_i * f_i
replicatorField x f i = x_i * (f_i - avgFitness x f).
```

The repository is available at:

<https://github.com/velvetmonkey/replicator-lean>

## 3. Theorem Inventory

The source contains seven headline theorem-level results.

### Layer 1 - Simplex Invariance

1. `simplex_invariant` proves that the vector-field components sum to zero on the simplex:

```text
InSimplex x -> sum_i replicatorField x f i = 0.
```

This is the mass-conservation identity behind positive invariance of the simplex.

### Layer 2 - Fixed Points and Nash Equilibria

2. `replicator_fixed_point` characterises fixed points:

```text
IsFixedPoint x f
  iff forall i, 0 < x_i -> f_i = avgFitness x f.
```

3. `nash_is_fixed_point` proves that every Nash equilibrium is a fixed point:

```text
IsNashEquilibrium x f -> IsFixedPoint x f.
```

Here `IsNashEquilibrium x f` means that `x` is in the simplex and every pure strategy earns at most the average fitness.

### Layer 3 - Lyapunov and Convergence Algebra

4. `potential_game_lyapunov` proves the instantaneous Lyapunov identity:

```text
sum_i f_i * replicatorField x f i = fitnessVariance x f.
```

In a potential game, where the fitness vector is the gradient of a potential, the left side is the potential derivative along the vector field.

5. `fitness_variance_nonneg` proves non-negativity of the variance:

```text
0 <= fitnessVariance x f.
```

6. `fitness_variance_eq_zero_iff` proves that zero variance is equivalent to being a fixed point:

```text
fitnessVariance x f = 0 iff IsFixedPoint x f.
```

7. `replicator_convergence` proves the algebraic convergence criterion:

```text
(IsFixedPoint x f and forall j, f_j <= avgFitness x f)
  iff IsNashEquilibrium x f.
```

## 4. Main Theorems

### Simplex Invariance

The theorem `simplex_invariant` expands the replicator field:

```text
sum_i x_i * (f_i - avgFitness x f).
```

Distributing the sum gives

```text
sum_i x_i f_i - avgFitness x f * sum_i x_i.
```

On the simplex, `sum_i x_i = 1`, and by definition `avgFitness x f = sum_i x_i f_i`, so the expression is zero.

### Fixed-Point Characterisation

The theorem `replicator_fixed_point` is the support condition for rest points. Since each component is

```text
x_i * (f_i - avgFitness x f),
```

vanishing of all components means that for each `i`, either `x_i = 0` or `f_i = avgFitness x f`. On the simplex, non-negativity lets the converse be stated as equality of fitness on the positive support.

### Lyapunov Identity

The theorem `potential_game_lyapunov` proves

```text
sum_i f_i * x_i * (f_i - avgFitness x f)
  = sum_i x_i * (f_i - avgFitness x f)^2.
```

The proof is algebraic: expand both sides, use `sum_i x_i = 1`, and identify the average fitness term. The right side is the population fitness variance.

### Variance Zero and the Convergence Criterion

The theorem `fitness_variance_eq_zero_iff` uses non-negativity of each term `x_i * (f_i - avgFitness x f)^2` to show that the variance vanishes exactly when every replicator-field component vanishes.

The theorem `replicator_convergence` then packages the Nash condition:

```text
IsFixedPoint x f and forall j, f_j <= avgFitness x f
```

as equivalent to `IsNashEquilibrium x f`, given the simplex hypothesis. This is the algebraic core used with the Lyapunov identity in potential-game convergence arguments.

## 5. Proof Sketch

`ReplicatorLean/Defs.lean` sets up all objects as finite sums over `Fin n`. This finite setting keeps the formal arguments algebraic and avoids measure theory or general ODE infrastructure.

`ReplicatorLean/Invariance.lean` proves mass invariance by unfolding `replicatorField` and `avgFitness`, distributing multiplication over subtraction, and using the simplex identity `sum_i x_i = 1`.

`ReplicatorLean/FixedPoints.lean` proves that fixed points are exactly support-equal-fitness states. It then proves `nash_is_fixed_point` by showing that the weighted sum of non-negative terms `x_i * (avgFitness x f - f_i)` is zero; each term must therefore vanish, and the replicator field is zero componentwise.

`ReplicatorLean/Convergence.lean` proves the Lyapunov identity by algebraic expansion, proves non-negativity by summing non-negative variance terms, and proves the zero-variance characterisation using the finite-sum zero criterion for non-negative summands. The final theorem `replicator_convergence` is a direct equivalence between the fixed-point-plus-Nash-inequality condition and the definition of Nash equilibrium.

## 6. Relation to Sibling Libraries

`replicator-lean` is closest to `lotka-volterra-lean`, which has DOI `10.5281/zenodo.20474669` and formalises population-dynamics invariants. The source documentation records the classical Hofbauer connection: replicator dynamics with linear fitness can be transformed into a generalised Lotka-Volterra system on positive coordinates.

It also relates to `lyapunov-odes-lean`, DOI `10.5281/zenodo.20475912`, and `lasalle-lean`, DOI `10.5281/zenodo.20476034`. Those libraries formalise general Lyapunov and invariance-principle patterns. `replicator-lean` supplies the finite-dimensional algebra that identifies the Lyapunov derivative and its zero set for potential games.

Finally, `gradient-descent-lean`, DOI `10.5281/zenodo.20472996`, and `langevin-lean` share the same broad theme: local algebraic identities become global convergence claims when paired with an appropriate dynamical or recurrence principle. In `replicator-lean`, the local identity is fitness variance.

## 7. Conclusion

`replicator-lean` provides a compact Lean 4 / Mathlib formalisation of the core algebra of replicator dynamics on the standard simplex. It proves simplex mass invariance, the support characterisation of fixed points, Nash equilibria as fixed points, the potential-game Lyapunov identity, non-negativity of fitness variance, the equivalence between zero variance and fixed points, and the algebraic convergence criterion relating fixed points and Nash equilibria.

Future work could connect these algebraic lemmas to a formal ODE theory of replicator trajectories, instantiate the library for matrix games with state-dependent fitness `f(x) = A x`, and combine it with a formal LaSalle invariance theorem to obtain trajectory-level convergence to Nash equilibrium sets.

## References

Taylor, P. D. and Jonker, L. B. (1978). *Evolutionarily stable strategies and game dynamics*. Mathematical Biosciences, 40(1-2), 145-156.

Hofbauer, J. (1981). *On the occurrence of limit cycles in the Volterra-Lotka equation*. Nonlinear Analysis, 5(9), 1003-1007.

Hofbauer, J. and Sigmund, K. (1998). *Evolutionary Games and Population Dynamics*. Cambridge University Press.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *lotka-volterra-lean: Formal Proofs of Hamiltonian Conservation and Positive Invariance in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20474669>

Cassie, B. (2026). *lyapunov-odes-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20475912>

Cassie, B. (2026). *lasalle-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20476034>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>
