import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Poly

/-- A complex polynomial of degree at least two eventually dominates the linear growth
`z ↦ 2‖z‖`: the leading term `a z^n` beats the lower order terms once `‖z‖` is large. -/
private theorem exists_bound_polynomial_eval (P : Polynomial ℂ) (hn : 2 ≤ P.natDegree) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖P.eval z‖ := by
  have hP : P ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have ha : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hapos : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr ha
  refine ⟨max 1 (((P.natDegree : ℝ) * P.supNorm + 2) / ‖P.leadingCoeff‖), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro z hz
    have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have hzR : ((P.natDegree : ℝ) * P.supNorm + 2) / ‖P.leadingCoeff‖ ≤ ‖z‖ :=
      le_trans (le_max_right _ _) hz
    have hM2 : (P.natDegree : ℝ) * P.supNorm + 2 ≤ ‖P.leadingCoeff‖ * ‖z‖ := by
      have h := mul_le_mul_of_nonneg_left hzR (norm_nonneg P.leadingCoeff)
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hapos)] at h
      exact h
    have hsplit : P.eval z = (∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i)
        + P.leadingCoeff * z ^ P.natDegree := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
      rfl
    have hS : ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i‖
        ≤ (P.natDegree : ℝ) * P.supNorm * ‖z‖ ^ (P.natDegree - 1) := by
      calc ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i‖
          ≤ ∑ i ∈ Finset.range P.natDegree, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖ * ‖z‖ ^ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_mul, norm_pow]
        _ ≤ ∑ i ∈ Finset.range P.natDegree, P.supNorm * ‖z‖ ^ (P.natDegree - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            exact mul_le_mul (Polynomial.le_supNorm P i)
              (pow_le_pow_right₀ hz1 (Nat.le_pred_of_lt hi))
              (by positivity) (Polynomial.supNorm_nonneg P)
        _ = (P.natDegree : ℝ) * P.supNorm * ‖z‖ ^ (P.natDegree - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have hrev : ‖P.leadingCoeff * z ^ P.natDegree‖
        - ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i‖ ≤ ‖P.eval z‖ := by
      rw [hsplit]
      have h := norm_sub_norm_le (P.leadingCoeff * z ^ P.natDegree)
        (-(∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i))
      simpa [norm_neg, sub_neg_eq_add, add_comm] using h
    have hnormT : ‖P.leadingCoeff * z ^ P.natDegree‖
        = ‖P.leadingCoeff‖ * ‖z‖ ^ P.natDegree := by
      rw [norm_mul, norm_pow]
    have hpow : ‖z‖ ≤ ‖z‖ ^ (P.natDegree - 1) := by
      have h1 : (1 : ℕ) ≤ P.natDegree - 1 := by omega
      simpa using pow_le_pow_right₀ hz1 h1
    have hBA : (2 : ℝ) ≤ ‖P.leadingCoeff‖ * ‖z‖ - (P.natDegree : ℝ) * P.supNorm := by
      linarith
    have hps : ‖z‖ ^ P.natDegree = ‖z‖ ^ (P.natDegree - 1) * ‖z‖ := by
      conv_lhs => rw [show P.natDegree = (P.natDegree - 1) + 1 by omega, pow_succ]
    have halg : ‖z‖ ^ (P.natDegree - 1)
          * (‖P.leadingCoeff‖ * ‖z‖ - (P.natDegree : ℝ) * P.supNorm)
        = ‖P.leadingCoeff‖ * ‖z‖ ^ P.natDegree
          - (P.natDegree : ℝ) * P.supNorm * ‖z‖ ^ (P.natDegree - 1) := by
      rw [hps]; ring
    calc 2 * ‖z‖ = ‖z‖ * 2 := by ring
      _ ≤ ‖z‖ ^ (P.natDegree - 1)
            * (‖P.leadingCoeff‖ * ‖z‖ - (P.natDegree : ℝ) * P.supNorm) := by
            have hh := mul_le_mul hpow hBA (by norm_num) (by positivity)
            linarith
      _ = ‖P.leadingCoeff‖ * ‖z‖ ^ P.natDegree
            - (P.natDegree : ℝ) * P.supNorm * ‖z‖ ^ (P.natDegree - 1) := halg
      _ ≤ ‖P.leadingCoeff‖ * ‖z‖ ^ P.natDegree
            - ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i‖ := by linarith
      _ = ‖P.leadingCoeff * z ^ P.natDegree‖
            - ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * z ^ i‖ := by rw [hnormT]
      _ ≤ ‖P.eval z‖ := hrev

theorem isPolynomialMap_basinEscape {F : ℂ → ℂ}
    (h : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : Work.FatouParabolic.BasinEscape F := by
  obtain ⟨P, hn, hF⟩ := h
  obtain ⟨R, hRpos, hR⟩ := exists_bound_polynomial_eval P hn
  refine ⟨R, hRpos, fun z hz => ?_⟩
  rw [hF z]
  exact hR z hz

end Work.FatouParabolic.Poly
