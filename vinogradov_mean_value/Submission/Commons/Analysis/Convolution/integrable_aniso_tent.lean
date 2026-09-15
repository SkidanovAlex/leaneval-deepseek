import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory
open scoped BigOperators

namespace Commons.Analysis.Convolution

/-- On `Fin k → ℝ` (with the sup-norm of the product) the supremum of the absolute
values of the coordinates is the norm. -/
lemma sup'_abs_eq_norm {k : ℕ} (hk : 1 ≤ k) (y : Fin k → ℝ) :
    (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => |y i|)
      = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    simpa using (pi_norm_le_iff_of_nonneg (norm_nonneg y)).1 le_rfl i
  · refine (pi_norm_le_iff_of_nonneg ?_).2 (fun i => ?_)
    · exact le_trans (abs_nonneg (y ⟨0, hk⟩))
        (Finset.le_sup' (fun i => |y i|) (Finset.mem_univ (⟨0, hk⟩ : Fin k)))
    · simpa using Finset.le_sup' (fun i => |y i|) (Finset.mem_univ i)

/-- The anisotropic tent `(max 1 (max_i |y i|))^{-A}` is integrable on `ℝ^k` as soon
as `A > k`: it is dominated by `2^A (1 + ‖y‖)^{-A}`, and the latter is integrable by
`integrable_one_add_norm` since the dimension `k` is less than `A`. -/
theorem integrable_aniso_tent (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) :
    MeasureTheory.Integrable (fun y : Fin k → ℝ =>
      (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |y i|)) ^ (-A)) := by
  have hApos : 0 < A := lt_of_le_of_lt (Nat.cast_nonneg k) hA
  rw [show (fun y : Fin k → ℝ =>
        (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          fun i => |y i|)) ^ (-A))
      = (fun y : Fin k → ℝ => (max 1 ‖y‖) ^ (-A)) from by
        funext y; rw [sup'_abs_eq_norm hk y]]
  have hfin : (Module.finrank ℝ (Fin k → ℝ) : ℝ) < A := by
    rw [Module.finrank_fin_fun]; exact hA
  have hbase : Integrable (fun y : Fin k → ℝ => (1 + ‖y‖) ^ (-A)) :=
    integrable_one_add_norm (μ := volume) hfin
  refine Integrable.mono' (hbase.const_mul ((2 : ℝ) ^ A)) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    apply Continuous.rpow_const
    · exact Continuous.max continuous_const continuous_norm
    · intro y; left
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖))
  · refine Filter.Eventually.of_forall (fun y => ?_)
    have hMpos : 0 < max 1 ‖y‖ := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hMpos) (-A))]
    have hle : 1 + ‖y‖ ≤ 2 * max 1 ‖y‖ := by
      have h := add_le_add (le_max_left (1 : ℝ) ‖y‖) (le_max_right (1 : ℝ) ‖y‖)
      linarith
    have h2 : (2 : ℝ) ^ (-A) * (max 1 ‖y‖) ^ (-A) ≤ (1 + ‖y‖) ^ (-A) := by
      calc (2 : ℝ) ^ (-A) * (max 1 ‖y‖) ^ (-A)
          = (2 * max 1 ‖y‖) ^ (-A) := by
            rw [Real.mul_rpow (by norm_num) (le_of_lt hMpos)]
        _ ≤ (1 + ‖y‖) ^ (-A) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    have h2A : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
    calc (max 1 ‖y‖) ^ (-A)
        = (2 : ℝ) ^ A * ((2 : ℝ) ^ (-A) * (max 1 ‖y‖) ^ (-A)) := by
            rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel,
              Real.rpow_zero, one_mul]
      _ ≤ (2 : ℝ) ^ A * (1 + ‖y‖) ^ (-A) := mul_le_mul_of_nonneg_left h2 (le_of_lt h2A)

end Commons.Analysis.Convolution