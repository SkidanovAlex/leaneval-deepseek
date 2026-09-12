import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

lemma sum_log_norm_interval {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (v : Fin k → E) (c0 c1 C : ℝ) (hc0 : 0 < c0) (hc1 : 0 < c1) (hC0 : 0 < C)
    (hlo : ∀ i, (c0 * C) ≤ ‖v i‖) (hhi : ∀ i, ‖v i‖ ≤ (c1 * C)) :
    (k : ℝ) * Real.log (c0 * C) ≤ (∑ i : Fin k, Real.log ‖v i‖) ∧
      (∑ i : Fin k, Real.log ‖v i‖) ≤ (k : ℝ) * Real.log (c1 * C) := by
  have hc0C_pos : 0 < c0 * C := mul_pos hc0 hC0
  have hnorm_pos : ∀ i : Fin k, 0 < ‖v i‖ := fun i => lt_of_lt_of_le hc0C_pos (hlo i)
  constructor
  · have hterm : ∀ i : Fin k, Real.log (c0 * C) ≤ Real.log ‖v i‖ :=
      fun i => Real.log_le_log hc0C_pos (hlo i)
    calc
      (k : ℝ) * Real.log (c0 * C) = ∑ _ : Fin k, Real.log (c0 * C) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin k, Real.log ‖v i‖ := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
  · have hterm : ∀ i : Fin k, Real.log ‖v i‖ ≤ Real.log (c1 * C) :=
      fun i => Real.log_le_log (hnorm_pos i) (hhi i)
    calc
      (∑ i : Fin k, Real.log ‖v i‖) ≤ ∑ _ : Fin k, Real.log (c1 * C) := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = (k : ℝ) * Real.log (c1 * C) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

end Commons.Analysis.Real