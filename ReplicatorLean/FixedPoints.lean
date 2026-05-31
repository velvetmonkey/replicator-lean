/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: replicator-lean
-/
import ReplicatorLean.Defs

/-!
# Fixed Points of Replicator Dynamics

## Main Results

* `replicator_fixed_point` — `x` is a fixed point of the replicator dynamics iff
  `fᵢ = x̄·f` for every strategy i in the support (xᵢ > 0).
* `nash_is_fixed_point` — every Nash equilibrium is a fixed point.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-
**Fixed-point characterisation**: `x` is a fixed point of the replicator dynamics
    if and only if every strategy in the support earns exactly the average fitness.

    ẋᵢ = xᵢ(fᵢ − x̄·f) = 0  for all i
    ⟺  for all i, xᵢ = 0 ∨ fᵢ = x̄·f
    ⟺  for all i with xᵢ > 0, fᵢ = x̄·f.
-/
theorem replicator_fixed_point (x f : Fin n → ℝ) (hx : InSimplex x) :
    IsFixedPoint x f ↔ ∀ i, 0 < x i → f i = avgFitness x f := by
  constructor <;> intro h <;> simp_all +decide [ IsFixedPoint, replicatorField ];
  · exact fun i hi => eq_of_sub_eq_zero ( Or.resolve_left ( h i ) hi.ne' );
  · exact fun i => Classical.or_iff_not_imp_left.2 fun hi => sub_eq_zero.2 <| h i <| lt_of_le_of_ne ( hx.1 i ) ( Ne.symm hi )

/-
**Nash equilibria are fixed points**.
    If `x` is a Nash equilibrium (fⱼ ≤ x̄·f for all j, with x ∈ Δₙ),
    then `x` is a fixed point of the replicator dynamics.

    *Proof sketch*: For i with xᵢ > 0 we have fᵢ ≤ x̄·f (Nash condition).
    But x̄·f = Σⱼ xⱼ fⱼ ≤ Σⱼ xⱼ · x̄·f = x̄·f (since each fⱼ ≤ x̄·f),
    with equality iff fⱼ = x̄·f whenever xⱼ > 0.  Since the weighted average
    of values ≤ c equals c only when all values in the support equal c, we
    get fᵢ = x̄·f for every i with xᵢ > 0.  By `replicator_fixed_point`
    this means `x` is a fixed point.
-/
theorem nash_is_fixed_point (x f : Fin n → ℝ) (hx : IsNashEquilibrium x f) :
    IsFixedPoint x f := by
  obtain ⟨ hx₁, hx₂ ⟩ := hx;
  -- By definition of `avgFitness`, we know that `avgFitness x f = ∑ i, x i * f i`.
  have h_avg : ∑ i, x i * (avgFitness x f - f i) = 0 := by
    simp +decide [ mul_sub, ← Finset.sum_mul _ _ _, hx₁.2, avgFitness ];
  -- Since each term in the sum is non-negative and their sum is zero, each term must be zero.
  have h_zero : ∀ i, x i * (avgFitness x f - f i) = 0 := by
    exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => mul_nonneg ( hx₁.1 i ) ( sub_nonneg.2 ( hx₂ i ) ) ) ( Finset.mem_univ i ) ) h_avg.le ) ( mul_nonneg ( hx₁.1 i ) ( sub_nonneg.2 ( hx₂ i ) ) );
  intro i; specialize h_zero i; simp_all +decide [ sub_eq_iff_eq_add ] ;
  cases h_zero <;> simp +decide [ *, replicatorField ]

end