import Mathlib
import Submission.Work.Drive.polarParam

/-!
# The defining identity of `(dirParam, radParam)`

This file proves the fundamental property of the polar-coordinate pair of
`Submission/Work/Drive/polarParam.lean`: for every `z` of the closed unit disk,

`z = (1 - 2 radParam z) · exp (π i dirParam z)`,

with `dirParam z ∈ [0,1)` and `radParam z ∈ [0,1]`.

The proof is a three-case analysis on `Complex.arg z` (`arg z = π`; `0 ≤ arg z < π`;
`arg z < 0`), in each case using the polar decomposition
`‖z‖ · exp (arg z · i) = z` (`Complex.norm_mul_exp_arg_mul_I`) and, in the third case,
`exp (π i) = -1` and periodicity along the branch `t = arg z / π + 1`.
-/

noncomputable section

namespace Work.Drive

theorem dirParam_radParam (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Work.Drive.dirParam z ∈ Set.Ico 0 1 ∧ Work.Drive.radParam z ∈ Set.Icc 0 1 ∧
      ((1 - 2 * Work.Drive.radParam z : ℝ) : ℂ) *
        Complex.exp (Real.pi * ((Work.Drive.dirParam z : ℝ) : ℂ) * Complex.I) = z := by
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey : (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) = z :=
    Complex.norm_mul_exp_arg_mul_I z
  have hrad_hi : ((1 + ‖z‖) / 2) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> linarith [norm_nonneg z]
  have hrad_lo : ((1 - ‖z‖) / 2) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> linarith [norm_nonneg z]
  by_cases hπ : z.arg = Real.pi
  · have hd : dirParam z = 0 := by simp [dirParam, hπ]
    have hr : radParam z = (1 + ‖z‖) / 2 := by simp [radParam, hπ]
    have hz_eq : z = -(‖z‖ : ℂ) := by
      have h := hkey
      rw [hπ] at h
      rw [Complex.exp_pi_mul_I, mul_neg_one] at h
      exact h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [hd]; exact ⟨le_refl 0, zero_lt_one⟩
    · rw [hr]; exact hrad_hi
    · have hexp : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
      have hc : (1 - 2 * ((1 + ‖z‖) / 2) : ℝ) = -‖z‖ := by ring
      rw [hd, hr, hexp, mul_one, hc, Complex.ofReal_neg]
      exact hz_eq.symm
  · by_cases h0 : 0 ≤ z.arg
    · have hd : dirParam z = z.arg / Real.pi := by simp [dirParam, hπ, h0]
      have hr : radParam z = (1 - ‖z‖) / 2 := by simp [radParam, hπ, h0]
      have harg_lt : z.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi z) hπ
      refine ⟨?_, ?_, ?_⟩
      · rw [hd, Set.mem_Ico]
        exact ⟨div_nonneg h0 (le_of_lt hπpos), by rw [div_lt_one hπpos]; exact harg_lt⟩
      · rw [hr]; exact hrad_lo
      · have h1 : ((Real.pi : ℝ) : ℂ) * ((z.arg / Real.pi : ℝ) : ℂ) = (z.arg : ℂ) := by
          rw [← Complex.ofReal_mul, mul_div_cancel₀ z.arg Real.pi_ne_zero]
        have hexp : Complex.exp (Real.pi * ((z.arg / Real.pi : ℝ) : ℂ) * Complex.I) =
            Complex.exp ((z.arg : ℂ) * Complex.I) := by rw [h1]
        have hc : (1 - 2 * ((1 - ‖z‖) / 2) : ℝ) = ‖z‖ := by ring
        rw [hd, hr, hexp, hc]
        exact hkey
    · have hneg : z.arg < 0 := lt_of_not_ge h0
      have hd : dirParam z = z.arg / Real.pi + 1 := by simp [dirParam, hπ, h0]
      have hr : radParam z = (1 + ‖z‖) / 2 := by simp [radParam, hπ, h0]
      refine ⟨?_, ?_, ?_⟩
      · rw [hd, Set.mem_Ico]
        constructor
        · have h2 : (-1 : ℝ) < z.arg / Real.pi := by
            rw [lt_div_iff₀ hπpos]; linarith [Complex.neg_pi_lt_arg z]
          linarith
        · have h2 : z.arg / Real.pi < 0 := div_neg_of_neg_of_pos hneg hπpos
          linarith
      · rw [hr]; exact hrad_hi
      · have hp : Real.pi * (z.arg / Real.pi + 1) = z.arg + Real.pi := by
          rw [mul_add, mul_div_cancel₀ z.arg Real.pi_ne_zero, mul_one]
        have h1 : ((Real.pi : ℝ) : ℂ) * ((z.arg / Real.pi + 1 : ℝ) : ℂ) =
            ((z.arg + Real.pi : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, hp]
        have hexp : Complex.exp (Real.pi * ((z.arg / Real.pi + 1 : ℝ) : ℂ) * Complex.I) =
            - Complex.exp ((z.arg : ℂ) * Complex.I) := by
          rw [h1, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
          ring
        have hc : (1 - 2 * ((1 + ‖z‖) / 2) : ℝ) = -‖z‖ := by ring
        rw [hd, hr, hexp, hc, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg]
        exact hkey

end Work.Drive
