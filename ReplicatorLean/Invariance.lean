/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: replicator-lean
-/
import ReplicatorLean.Defs

/-!
# Simplex Invariance under Replicator Dynamics

The key algebraic fact behind simplex invariance: the components of the
replicator vector field always sum to zero, so Σᵢ ẋᵢ = 0.  Geometrically
this means that the hyperplane Σxᵢ = 1 is invariant, and together with
non-negativity preservation this makes the simplex positively invariant.

## Main Results

* `simplex_invariant` — Σᵢ ẋᵢ = 0 for the replicator vector field.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-
**Simplex invariance**: the replicator vector field components sum to zero.

    Σᵢ xᵢ (fᵢ − x̄·f) = Σᵢ xᵢ fᵢ − x̄·f · Σᵢ xᵢ .

    When `x ∈ Δₙ` (so Σxᵢ = 1) this equals  x̄·f − x̄·f = 0.

    This is the fundamental algebraic identity that guarantees positive
    invariance of the simplex under the replicator ODE.
-/
theorem simplex_invariant (x f : Fin n → ℝ) (hx : InSimplex x) :
    ∑ i, replicatorField x f i = 0 := by
  unfold replicatorField;
  unfold avgFitness;
  simp +decide [mul_sub, ← Finset.sum_mul, hx.2]

end