/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: replicator-lean
-/
import Mathlib

/-!
# Replicator Dynamics — Core Definitions

This module defines the fundamental objects for studying replicator dynamics
on the standard simplex Δₙ ⊆ ℝⁿ.

## Main Definitions

* `InSimplex` — predicate for membership in the standard simplex
* `avgFitness` — average (mean) fitness of a population: x̄·f = Σᵢ xᵢ fᵢ
* `replicatorField` — the replicator vector field: ẋᵢ = xᵢ (fᵢ − x̄·f)
* `IsFixedPoint` — fixed point of replicator dynamics
* `IsNashEquilibrium` — Nash equilibrium (every strategy earns at most the average)
* `fitnessVariance` — population variance of fitness: Var_x(f) = Σᵢ xᵢ (fᵢ − x̄·f)²
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-! ### The Standard Simplex -/

/-- A vector `x : Fin n → ℝ` lies in the standard simplex Δₙ when all
    coordinates are non-negative and they sum to one. -/
def InSimplex (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-! ### Fitness and Replicator Vector Field -/

/-- Average (mean) fitness of the population: x̄·f = Σᵢ xᵢ fᵢ. -/
def avgFitness (x f : Fin n → ℝ) : ℝ :=
  ∑ i, x i * f i

/-- The replicator vector field.
    The i-th component is  ẋᵢ = xᵢ · (fᵢ − x̄·f). -/
def replicatorField (x f : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * (f i - avgFitness x f)

/-! ### Fixed Points and Nash Equilibria -/

/-- `x` is a fixed point of the replicator dynamics with fitness `f` when
    the replicator vector field vanishes: ẋᵢ = 0 for every i. -/
def IsFixedPoint (x f : Fin n → ℝ) : Prop :=
  ∀ i, replicatorField x f i = 0

/-- `x` is a Nash equilibrium (of the symmetric game with fitness `f` at state `x`)
    when `x ∈ Δₙ` and no pure strategy earns more than the population average:
    fⱼ ≤ x̄·f for every j. -/
def IsNashEquilibrium (x f : Fin n → ℝ) : Prop :=
  InSimplex x ∧ ∀ j, f j ≤ avgFitness x f

/-! ### Fitness Variance -/

/-- The fitness variance under population state `x`:
    Var_x(f) = Σᵢ xᵢ (fᵢ − x̄·f)².  This is always non-negative on the simplex. -/
def fitnessVariance (x f : Fin n → ℝ) : ℝ :=
  ∑ i, x i * (f i - avgFitness x f) ^ 2

end
