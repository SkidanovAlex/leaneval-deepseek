import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.mfun_im_shift

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `Im m(E,·) ≥ Im E` for `Im E > 0`: the `m`-function takes values at least `Im E`
above the real axis.  Immediate from the covariance relation. -/
theorem mfun_im_ge_self (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    E.im ≤ (mfun α lam E y).im := by
  have h := mfun_im_shift α lam E hE (y - α)
  rw [sub_add_cancel] at h
  rw [h]
  have hnn : 0 ≤ (mfun α lam E (y - α)).im / ‖mfun α lam E (y - α)‖ ^ 2 :=
    div_nonneg (le_of_lt (MfunProbs.mfun_im_pos α lam hE (y - α)))
      (by positivity)
  linarith

/-- For `w : ℂ`, `Im (1/conj w) = Im w / ‖w‖²`. -/
theorem im_one_div_star (w : ℂ) : (1 / star w).im = w.im / ‖w‖ ^ 2 := by
  rw [one_div, Complex.star_def, ← Complex.conj_inv]
  rw [Complex.conj_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

/-- `sigSec` is `ℍ`-valued. -/
theorem sigSec_im_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    0 < (sigSec α lam E y).im := by
  have hm0 : mfun α lam E (α - y) ≠ 0 := by
    intro h0
    have h := MfunProbs.mfun_im_pos α lam hE (α - y)
    rw [h0] at h; simp at h
  rw [sigSec, im_one_div_star]
  exact div_pos (MfunProbs.mfun_im_pos α lam hE (α - y))
    (pow_pos (norm_pos_iff.mpr hm0) 2)

/-- `glued` on the upper half plane is `mfun`. -/
theorem glued_of_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    glued α lam E y = mfun α lam E y := by
  rw [glued, if_pos hE]

/-- Below the axis, `glued` is the reflected section `sigSec` (with `E` the reflection). -/
theorem glued_of_neg (α lam : ℝ) {E E' : ℂ} (hE' : E'.im < 0) (hstar : star E' = E) (y : ℝ) :
    glued α lam E' y = sigSec α lam E y := by
  rw [glued, if_neg (not_lt.mpr (le_of_lt hE')), sigSec, hstar]

/-- If `im X = N > 0`, then `‖-1/X‖ ≤ 1/N`. -/
theorem inv_norm_le (X : ℂ) {N : ℝ} (hXim : X.im = N) (hN : 0 < N) :
    ‖-1 / X‖ ≤ 1 / N := by
  have h : ‖-1 / X‖ = 1 / ‖X‖ := by
    simp only [norm_div, norm_neg, norm_one]
  rw [h]
  exact one_div_le_one_div_of_le hN (by rw [← hXim]; exact Complex.im_le_norm X)

/-- The jump bound: if `im X = N₁ > 0` and `im Y = N₂ > 0`, then
`‖-1/X - -1/Y‖ ≤ ‖X - Y‖/(N₁ N₂)`. -/
theorem jump_norm_le (X Y : ℂ) {N₁ N₂ : ℝ} (hXim : X.im = N₁) (hYim : Y.im = N₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    ‖-1 / X - -1 / Y‖ ≤ ‖X - Y‖ / (N₁ * N₂) := by
  have hXne : X ≠ 0 := by
    intro h; rw [h] at hXim; simp at hXim; linarith
  have hYne : Y ≠ 0 := by
    intro h; rw [h] at hYim; simp at hYim; linarith
  have hkey : -1 / X - -1 / Y = (X - Y) / (X * Y) := by
    field_simp
    ring
  rw [hkey, norm_div, norm_mul]
  refine div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hN₁ hN₂) ?_
  exact mul_le_mul (by rw [← hXim]; exact Complex.im_le_norm X)
    (by rw [← hYim]; exact Complex.im_le_norm Y) (le_of_lt hN₂) (norm_nonneg _)

theorem Psi_bounds (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖Work.TMComp.Kotani.Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y‖
        ≤ 1 / Work.TMComp.Kotani.N1 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y ∧
      ‖Work.TMComp.Kotani.Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y‖
        ≤ 1 / Work.TMComp.Kotani.N2 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y ∧
      ‖Work.TMComp.Kotani.Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          - Work.TMComp.Kotani.Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y‖
        ≤ ‖Work.TMComp.Kotani.mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
              - Work.TMComp.Kotani.sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
              - (ε : ℂ) * Complex.I‖
          / (Work.TMComp.Kotani.N1 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
              * Work.TMComp.Kotani.N2 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y) := by
  set E : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hEdef
  set E' : ℂ := (E₀ : ℂ) - (ε : ℂ) * Complex.I with hEpdef
  have hEim : E.im = ε := by
    rw [hEdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hEpim : E'.im = -ε := by
    rw [hEpdef]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hEpos : 0 < E.im := by rw [hEim]; exact hε
  have hEpneg : E'.im < 0 := by rw [hEpim]; linarith
  have hstar : star E' = E := by
    rw [hEdef, hEpdef]
    simp only [Complex.star_def, star_sub, star_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hglued_up : glued α lam E y = mfun α lam E y := glued_of_pos α lam hEpos y
  have hglued_dn : glued α lam E' y = sigSec α lam E y := glued_of_neg α lam hEpneg hstar y
  have hN1 : 0 < N1 α lam E y := by
    rw [N1, hEim]
    have := mfun_im_ge_self α lam hEpos y
    linarith
  have hN2 : 0 < N2 α lam E y := by
    rw [N2, hEim]
    have := sigSec_im_pos α lam hEpos y
    linarith
  have hhalf : (E / 2).im = E.im / 2 := by simp
  have hhalf' : (E' / 2).im = E'.im / 2 := by simp
  have hXim : (mfun α lam E y - E / 2).im = N1 α lam E y := by
    rw [Complex.sub_im, hhalf, N1]
  have hYim : (sigSec α lam E y - E' / 2).im = N2 α lam E y := by
    rw [Complex.sub_im, hhalf', N2, hEpim, hEim]
    ring
  have hXY : (mfun α lam E y - E / 2) - (sigSec α lam E y - E' / 2)
      = mfun α lam E y - sigSec α lam E y - (ε : ℂ) * Complex.I := by
    rw [hEdef, hEpdef]
    ring
  have hPsi_up : Psi α lam E y = -1 / (mfun α lam E y - E / 2) := by
    rw [Psi, hglued_up]
  have hPsi_dn : Psi α lam E' y = -1 / (sigSec α lam E y - E' / 2) := by
    rw [Psi, hglued_dn]
  refine ⟨?_, ?_, ?_⟩
  · rw [hPsi_up]
    exact inv_norm_le (mfun α lam E y - E / 2) hXim hN1
  · rw [hPsi_dn]
    exact inv_norm_le (sigSec α lam E y - E' / 2) hYim hN2
  · rw [hPsi_up, hPsi_dn, ← hXY]
    exact jump_norm_le (mfun α lam E y - E / 2) (sigSec α lam E y - E' / 2) hXim hYim hN1 hN2

end Work.TMComp.Kotani
