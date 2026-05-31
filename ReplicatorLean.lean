import ReplicatorLean.Defs
import ReplicatorLean.Invariance
import ReplicatorLean.FixedPoints
import ReplicatorLean.Convergence

/-!
# Replicator Dynamics on the Simplex — replicator-lean

A Lean 4 / Mathlib library formalising the core theory of replicator
dynamics in evolutionary game theory.

## Module structure

* `Defs` — core definitions (simplex, fitness, replicator field, Nash, variance)
* `Invariance` — simplex invariance (Σ ẋᵢ = 0)
* `FixedPoints` — fixed-point characterisation and Nash ⟹ fixed point
* `Convergence` — Lyapunov theory for potential games and convergence
-/
