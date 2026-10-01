import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_Q1_lower
import Submission.Work.LinnikAreas.Density4.W_pow_le_kappa
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_le_kappa

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- Pointwise lower bound for the summand of `tdQ`: for `2 ≤ n ≤ ⌊exp M⌋₊`
the factor `M - log n - 1` is at least `-1` (because `n ≤ exp M` forces `log n ≤ M`),
and `tdH` is nonnegative, whence
`(M - log n - 1) * tdH σ A n ≥ -tdH σ A n`. -/
lemma tdQ_summand_lower (σ A M : ℝ) (n : ℕ)
    (hn : n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊) :
    -(tdH σ A n) ≤ (M - Real.log (n:ℝ) - 1) * tdH σ A n := by
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ Real.exp M := by
    have h1 : (n : ℝ) ≤ (⌊Real.exp M⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    exact le_trans h1 (Nat.floor_le (Real.exp_pos M).le)
  have hnpos : 0 < (n : ℝ) := by
    have h : 0 < n := by omega
    exact_mod_cast h
  have hlog : Real.log (n : ℝ) ≤ M := by
    rw [Real.log_le_iff_le_exp hnpos]; exact hnN
  have hh : 0 ≤ tdH σ A n := by
    rw [tdH]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _) (Real.exp_pos _).le
  calc -(tdH σ A n) = (-1 : ℝ) * tdH σ A n := by ring
    _ ≤ (M - Real.log (n:ℝ) - 1) * tdH σ A n := by
        refine mul_le_mul_of_nonneg_right ?_ hh
        linarith

theorem tdQ_full_range_lower (σ A M : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : Real.exp M ≤ A) :
    -1000 * (Real.Gamma σ * A^σ)
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1) * Work.LinnikAreas.Density4.tdH σ A n := by
  have hGpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσ
  by_cases hA1 : 1 ≤ A
  · -- main case: `A ≥ 1`, use the global bound on the partial sums of the majorant
    have hk : 0 ≤ Real.Gamma σ * A ^ σ :=
      mul_nonneg hGpos.le (Real.rpow_nonneg (le_trans (Real.exp_pos M).le hA) σ)
    have hpt : ∀ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊,
        -(tdH σ A n) ≤ (M - Real.log (n:ℝ) - 1) * tdH σ A n :=
      fun n hn => tdQ_summand_lower σ A M n hn
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_neg_distrib] at hsum
    have hkappa := thetaDiag_sum_le_kappa σ A hσ hσ1 hA1 ⌊Real.exp M⌋₊
    linarith
  · have hAlt : A < 1 := not_le.mp hA1
    -- degenerate case: `A < 1` forces `exp M < 1` and the sum is empty
    have hexp_lt : Real.exp M < 1 := lt_of_le_of_lt hA hAlt
    have hN0 : ⌊Real.exp M⌋₊ = 0 := Nat.floor_eq_zero.mpr hexp_lt
    have hk : 0 ≤ Real.Gamma σ * A ^ σ := mul_nonneg hGpos.le (Real.rpow_nonneg (le_trans (Real.exp_pos M).le hA) σ)
    rw [hN0, Finset.Icc_eq_empty (by norm_num : ¬ (2:ℕ) ≤ 0), Finset.sum_empty]
    linarith

end Work.LinnikAreas.Density4
