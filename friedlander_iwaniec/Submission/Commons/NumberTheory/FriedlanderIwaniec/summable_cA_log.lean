import Mathlib
import Submission.Commons.Analysis.Series.summable_log_rpow_inv_div

namespace Commons.NumberTheory.FriedlanderIwaniec

open Filter

/-- If `c` decays like `(log y)^{-6}` (the shape of the Friedlander–Iwaniec hypothesis
`h24`), then `∑_d c d · log((d+1)/d)` is absolutely summable: `log((d+1)/d) ≤ 1/d`. -/
theorem summable_cA_log (c : ℕ → ℝ)
    (h24 : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → |c y| ≤ C * (Real.log y) ^ (-6 : ℝ)) :
    Summable (fun d : ℕ => c d * Real.log (((d : ℝ) + 1) / (d : ℝ))) := by
  obtain ⟨C, hCpos, hbound⟩ := h24
  -- The comparison series `∑ C · (log d)^{-6} / d`, which is summable since a `p > 1`
  -- Bertrand series `∑ (log n)^{-p}/n` converges.
  have hbase : Summable (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ (-6 : ℝ) / (d : ℝ))) :=
    (Commons.Analysis.Series.summable_log_rpow_inv_div 6 (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually hbase ?_
  rw [Nat.cofinite_eq_atTop]
  -- For all `d ≥ 2` we have `|c d| ≤ C (log d)^{-6}` and `log((d+1)/d) ≤ 1/d`.
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hlogpos : 0 < Real.log (d : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith)
  have hcd : |c d| ≤ C * (Real.log (d : ℝ)) ^ (-6 : ℝ) := hbound d hd
  have harg1 : (1 : ℝ) ≤ ((d : ℝ) + 1) / (d : ℝ) := by
    rw [le_div_iff₀ hd0]; linarith
  have hargpos : 0 < ((d : ℝ) + 1) / (d : ℝ) := by linarith
  have hlognn : 0 ≤ Real.log (((d : ℝ) + 1) / (d : ℝ)) := Real.log_nonneg harg1
  have hlog_le : Real.log (((d : ℝ) + 1) / (d : ℝ)) ≤ 1 / (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hargpos
    have heq : ((d : ℝ) + 1) / (d : ℝ) - 1 = 1 / (d : ℝ) := by
      rw [div_sub_one hd0.ne']; ring
    linarith [h, heq ▸ h]
  have hbnonneg : 0 ≤ C * (Real.log (d : ℝ)) ^ (-6 : ℝ) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg hlogpos.le (-6 : ℝ))
  have hstep : |c d| * Real.log (((d : ℝ) + 1) / (d : ℝ))
      ≤ (C * (Real.log (d : ℝ)) ^ (-6 : ℝ)) * (1 / (d : ℝ)) :=
    mul_le_mul hcd hlog_le hlognn hbnonneg
  have hrewrite : (C * (Real.log (d : ℝ)) ^ (-6 : ℝ)) * (1 / (d : ℝ))
      = C * ((Real.log (d : ℝ)) ^ (-6 : ℝ) / (d : ℝ)) := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlognn, ← hrewrite]
  exact hstep

end Commons.NumberTheory.FriedlanderIwaniec
