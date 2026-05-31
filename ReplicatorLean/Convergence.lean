/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: replicator-lean
-/
import ReplicatorLean.Defs
import ReplicatorLean.Invariance
import ReplicatorLean.FixedPoints

/-!
# Lyapunov Theory and Convergence for Potential Games

## Potential Games

A **potential game** is one where the fitness vector is the gradient of a
potential function φ.  Along a replicator trajectory x(t), the time
derivative of the potential is

    dφ/dt = Σᵢ fᵢ ẋᵢ = Σᵢ fᵢ xᵢ (fᵢ − x̄·f) = Var_x(f) ≥ 0.

The potential is therefore a **Lyapunov function** (non-decreasing along
trajectories), and its derivative vanishes precisely at fixed points.

## Main Results

* `potential_game_lyapunov` — the instantaneous Lyapunov derivative equals
  the fitness variance: Σᵢ fᵢ · ẋᵢ = Var_x(f).
* `fitness_variance_nonneg` — Var_x(f) ≥ 0 on the simplex.
* `fitness_variance_eq_zero_iff` — on the simplex, Var_x(f) = 0 iff x is
  a fixed point of replicator dynamics.
* `replicator_convergence` — for a strict potential game, a state on the
  simplex is a rest point of the Lyapunov dynamics iff it is a Nash
  equilibrium with uniform fitness across the support.

## Connection to Lotka–Volterra

**Remark (Hofbauer, 1981).**  Replicator dynamics on Δₙ with linear fitness
fᵢ(x) = (Ax)ᵢ is diffeomorphic to a generalised Lotka–Volterra system.
Setting yᵢ = xᵢ / xₙ for i < n and using the (n-1)-dimensional coordinate
chart that projects away the last component, the replicator ODE becomes

    ẏᵢ = yᵢ · ((A − Aₙ)y)ᵢ

which is a Lotka–Volterra system with interaction matrix  B = A − 1·Aₙ
(where Aₙ is the n-th row broadcast).  This coordinate change is a
diffeomorphism from the interior of Δₙ to ℝ₊ⁿ⁻¹.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-! ### Lyapunov identity -/

/-
**Lyapunov identity for potential games.**
    The dot product of the fitness vector with the replicator field equals
    the fitness variance:

      Σᵢ fᵢ · ẋᵢ  =  Σᵢ fᵢ · xᵢ (fᵢ − x̄·f)
                    =  Σᵢ xᵢ fᵢ² − x̄·f · Σᵢ xᵢ fᵢ
                    =  Σᵢ xᵢ fᵢ² − (x̄·f)²          (when Σxᵢ=1)
                    =  Var_x(f).

    In a potential game where fᵢ = ∂φ/∂xᵢ, the left-hand side is dφ/dt,
    so the potential is non-decreasing along replicator trajectories.
-/
theorem potential_game_lyapunov (x f : Fin n → ℝ) (hx : InSimplex x) :
    ∑ i, f i * replicatorField x f i = fitnessVariance x f := by
  unfold replicatorField fitnessVariance;
  simp +decide only [mul_sub, mul_left_comm, pow_two, mul_comm];
  simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, hx.2 ];
  unfold avgFitness; ring;

/-! ### Variance non-negativity -/

/-
The fitness variance is non-negative when `x ∈ Δₙ`.
-/
theorem fitness_variance_nonneg (x f : Fin n → ℝ) (hx : InSimplex x) :
    0 ≤ fitnessVariance x f := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg ( hx.1 i ) ( sq_nonneg _ )

/-! ### Variance zero characterisation -/

/-
On the simplex, the fitness variance vanishes iff every strategy in the
    support earns exactly the mean fitness — equivalently, iff `x` is a
    fixed point of the replicator dynamics.
-/
theorem fitness_variance_eq_zero_iff (x f : Fin n → ℝ) (hx : InSimplex x) :
    fitnessVariance x f = 0 ↔ IsFixedPoint x f := by
  unfold IsFixedPoint;
  -- By definition of fitness variance, we have that fitnessVariance x f = 0 if and only if xᵢ (fᵢ - x̄·f)² = 0 for all i.
  unfold fitnessVariance replicatorField;
  rw [ Finset.sum_eq_zero_iff_of_nonneg ];
  · grind +qlia;
  · exact fun i _ => mul_nonneg ( hx.1 i ) ( sq_nonneg _ )

/-! ### Convergence for strict potential games -/

/-
**Convergence criterion for strict potential games.**

    Combining the results above:

    1. `potential_game_lyapunov`: dφ/dt = Var_x(f) ≥ 0.
    2. `fitness_variance_eq_zero_iff`: Var_x(f) = 0 ⟺ x is a fixed point.
    3. `nash_is_fixed_point`: Nash equilibria are fixed points.

    For a **strict** potential game the converse of (3) also holds at interior
    points: a fixed point where all xᵢ > 0 and all fⱼ ≤ x̄·f is Nash.

    By LaSalle's invariance principle on the compact simplex, every
    trajectory converges to the largest invariant subset of {Var = 0},
    which is the set of Nash equilibria.

    We formalise the algebraic core: on the simplex, a fixed point where
    fⱼ ≤ x̄·f for all j is a Nash equilibrium, and Nash equilibria are
    exactly the rest points of the Lyapunov dynamics.
-/
theorem replicator_convergence (x f : Fin n → ℝ) (hx : InSimplex x) :
    (IsFixedPoint x f ∧ ∀ j, f j ≤ avgFitness x f) ↔ IsNashEquilibrium x f := by
  exact ⟨ fun h => ⟨ hx, h.2 ⟩, fun h => ⟨ nash_is_fixed_point x f h, h.2 ⟩ ⟩

end