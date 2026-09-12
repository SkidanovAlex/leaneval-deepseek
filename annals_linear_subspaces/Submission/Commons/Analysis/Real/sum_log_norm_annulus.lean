import Mathlib

/-!
# Log-sum interval from per-index annulus bounds

For a family `v : Fin k → E` in a normed group whose norms all lie in the annulus
`[10C, 12C]` (`C > 0`), the sum of the logarithms of the norms is trapped in the
corresponding interval:

`Σᵢ log‖v i‖ ∈ [k·log(10C), k·log(12C)]`.

This is the log-form of the annulus estimate used in the §3 Prop-5 wedge layer (the
per-index bounds `10C ≤ ‖v i‖ ≤ 12C` come from the block-lattice annulus theorems; taking
logarithms is legitimate since `‖v i‖ ≥ 10C > 0`).

Mathlib-only.
-/

noncomputable section

open scoped BigOperators
set_option autoImplicit false

namespace Commons.Analysis.Real

/-- **Log-interval from per-index annulus bounds**: if `10C ≤ ‖v i‖ ≤ 12C` for every index
of the `k`-family `v` (`C > 0`), then
`Σᵢ log‖v i‖ ∈ [k·log(10C), k·log(12C)]`. -/
lemma sum_log_norm_annulus {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (v : Fin k → E) (C : ℝ) (hC0 : 0 < C)
    (hlo : ∀ i, (10 * C) ≤ ‖v i‖) (hhi : ∀ i, ‖v i‖ ≤ (12 * C)) :
    (k : ℝ) * Real.log (10 * C) ≤ (∑ i : Fin k, Real.log ‖v i‖) ∧
      (∑ i : Fin k, Real.log ‖v i‖) ≤ (k : ℝ) * Real.log (12 * C) := by
  have hpos10 : 0 < (10 : ℝ) * C := by nlinarith
  have hpos : ∀ i, 0 < ‖v i‖ := fun i => lt_of_lt_of_le hpos10 (hlo i)
  have hloglo : ∀ i, Real.log (10 * C) ≤ Real.log ‖v i‖ := fun i =>
    Real.log_le_log hpos10 (hlo i)
  have hloghi : ∀ i, Real.log ‖v i‖ ≤ Real.log (12 * C) := fun i =>
    Real.log_le_log (hpos i) (hhi i)
  constructor
  · calc
      (k : ℝ) * Real.log (10 * C) = (∑ i : Fin k, Real.log (10 * C)) := by
        simp [Finset.sum_const, Fintype.card_fin]
      _ ≤ ∑ i : Fin k, Real.log ‖v i‖ := Finset.sum_le_sum (fun i hi => hloglo i)
  · calc
      (∑ i : Fin k, Real.log ‖v i‖) ≤ ∑ i : Fin k, Real.log (12 * C) :=
        Finset.sum_le_sum (fun i hi => hloghi i)
      _ = (k : ℝ) * Real.log (12 * C) := by
        simp [Finset.sum_const, Fintype.card_fin]

end Commons.Analysis.Real
