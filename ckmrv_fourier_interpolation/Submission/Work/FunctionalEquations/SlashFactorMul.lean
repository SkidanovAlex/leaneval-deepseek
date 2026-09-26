import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-- On the upper half plane the base `i/τ` of the slash factor has positive real part,
so its argument is not `π`; this is the hypothesis needed to invert the principal branch
of the complex power. -/
lemma slashFactor_base_re_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (Complex.I / τ).re := by
  rw [Complex.div_re]
  have h2 : (0 : ℝ) < Complex.normSq τ := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg τ.re, hτ]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_div, zero_add]
  exact div_pos hτ h2

/-- `i / (-1/τ) = (i/τ)⁻¹` for `τ ≠ 0`. -/
lemma slashFactor_base_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    Complex.I / (-1 / τ) = (Complex.I / τ)⁻¹ := by
  field_simp
  rw [Complex.I_sq]; norm_num

/-- **The slash factor `(i/τ)^{n/2}` is inverted by `τ ↦ -1/τ`.** -/
lemma slashFactor_neg_inv_eq_inv {n : ℕ} {τ : ℂ} (hτ : 0 < τ.im) :
    slashFactor n (-1 / τ) = (slashFactor n τ)⁻¹ := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have harg : (Complex.I / τ).arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [slashFactor_base_re_pos hτ]
  rw [slashFactor, slashFactor, slashFactor_base_neg_inv hτ0, Complex.inv_cpow _ _ harg]

theorem SlashFactorMul {n : ℕ} {τ : ℂ} (hτ : 0 < τ.im) :
    slashFactor n τ * slashFactor n (-1 / τ) = 1 := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hbase : Complex.I / τ ≠ 0 := by simp [Complex.I_ne_zero, hτ0]
  rw [slashFactor_neg_inv_eq_inv hτ, mul_inv_cancel₀]
  rw [slashFactor]
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)

end

end Work.FunctionalEquations
