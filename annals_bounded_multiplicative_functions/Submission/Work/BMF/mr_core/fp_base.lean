import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- Basic growth facts: for every `0 < ε ≤ 1` there is `L` such that for all `x ≥ L` the
six elementary inequalities used to seed the "large parameter" regime all hold. -/
theorem fp_base (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : ℝ, ∀ x : ℝ, L ≤ x →
      1 ≤ x ∧ 1 ≤ Real.log x ∧ 1 ≤ x ^ ((1 : ℝ) / 8) / ε ∧
      2 ≤ Real.exp (384 * Real.log x) ∧
      3 ≤ x ^ ((1 : ℝ) / 4) / ε ∧
      Real.exp (384 * Real.log x) ≤ Real.exp (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x)) := by
  refine ⟨max 1 (max (Real.exp 1) 81), ?_⟩
  intro x hx
  have h1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have h2 : Real.exp 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have h81 : (81 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) h2
    rwa [Real.log_exp] at this
  have hxnn : (0 : ℝ) ≤ x := by linarith
  have hpow8 : 1 ≤ x ^ ((1 : ℝ) / 8) := Real.one_le_rpow h1 (by norm_num)
  have hdiv1 : 1 ≤ x ^ ((1 : ℝ) / 8) / ε := by
    rw [le_div_iff₀ hε, one_mul]
    linarith
  have hpow4 : (3 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have h4eq : (x ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = x := by
      rw [← Real.rpow_mul hxnn ((1 : ℝ) / 4) (4 : ℝ),
        show ((1 : ℝ) / 4) * 4 = 1 by norm_num, Real.rpow_one]
    have h := (Real.rpow_le_rpow_iff (x := (3 : ℝ)) (y := x ^ ((1 : ℝ) / 4)) (z := (4 : ℝ))
        (by norm_num) (Real.rpow_nonneg hxnn _) (by norm_num)).mp
    apply h
    rw [h4eq]
    norm_num
    exact h81
  have hdiv3 : 3 ≤ x ^ ((1 : ℝ) / 4) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hexp2 : 2 ≤ Real.exp (384 * Real.log x) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2e
      rwa [Real.log_exp] at this
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (384 * Real.log x) := Real.exp_le_exp.mpr (by nlinarith)
  have hlast : Real.exp (384 * Real.log x) ≤
      Real.exp (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hnn : (0 : ℝ) ≤ 384 * Real.log x := by linarith
    calc 384 * Real.log x = 1 * (384 * Real.log x) := by ring
      _ ≤ (x ^ ((1 : ℝ) / 8) / ε) * (384 * Real.log x) :=
            mul_le_mul_of_nonneg_right hdiv1 hnn
  exact ⟨h1, hlog1, hdiv1, hexp2, hdiv3, hlast⟩

end Work.BMF.mr_core
