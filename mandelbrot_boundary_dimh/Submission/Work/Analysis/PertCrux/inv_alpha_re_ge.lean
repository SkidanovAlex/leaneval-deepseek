import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Re (1/α) ≥ (1/2) (Ξ'^2 + 1)^20` for `α ∈ 𝓕₁` with `‖α‖ ≤ (Ξ'^2 + 1)^{-20}`

`InF1 α` means `|α.im| < α.re`, i.e. `α` lies in the open cone `|arg α| < π/4` around the positive
real axis.  Hence `α.re ≥ ‖α‖ / √2`, so

`Re (1/α) = α.re / ‖α‖^2 ≥ 1/(√2 ‖α‖) ≥ (1/2) · 1/‖α‖ ≥ (1/2) (Ξ'^2 + 1)^20`.

The constant `1/2` is the safe rational substitute for `1/√2 = 0.707…`.
-/

namespace Work.Analysis.PertCrux

theorem inv_alpha_re_ge {Ξ' : ℝ} {α : ℂ} (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hαinv : (Ξ' ^ 2 + 1) ^ 20 ≤ 1 / ‖α‖) :
    (1 / 2) * (Ξ' ^ 2 + 1) ^ 20 ≤ (1 / α).re := by
  have habs : |α.im| < α.re := hinf
  have hrepos : 0 < α.re := lt_of_le_of_lt (abs_nonneg _) habs
  have hnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have him2 : α.im ^ 2 < α.re ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hrepos]; exact habs
  -- `‖α‖^2 = α.re^2 + α.im^2 ≤ 2 α.re^2`
  have hsq : ‖α‖ ^ 2 ≤ 2 * α.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hnorm2pos : 0 < ‖α‖ ^ 2 := by positivity
  -- multiply `hαinv` by `‖α‖^2 > 0`
  have hT_le : (Ξ' ^ 2 + 1) ^ 20 * ‖α‖ ^ 2 ≤ ‖α‖ := by
    have h1 : (Ξ' ^ 2 + 1) ^ 20 * ‖α‖ ^ 2 ≤ (1 / ‖α‖) * ‖α‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hαinv (by positivity)
    have h2 : (1 / ‖α‖) * ‖α‖ ^ 2 = ‖α‖ := by
      field_simp
    linarith
  -- `‖α‖ ≤ 2 α.re`
  have hsqrt2 : ‖α‖ ≤ 2 * α.re := by
    have h2 : ‖α‖ ^ 2 ≤ (2 * α.re) ^ 2 := by nlinarith
    have h := (sq_le_sq.mp h2)
    rw [abs_of_nonneg (norm_nonneg α), abs_of_nonneg (by linarith)] at h
    exact h
  simp only [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [le_div_iff₀ hnorm2pos]
  nlinarith [hT_le, hsqrt2]

end Work.Analysis.PertCrux
