import Mathlib
import Submission.Work.FIArea2.Sec6Defs
import Submission.Work.FIArea2.phiOf_comp_secScale
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Work.FIPlan

/-- `gnorm` is multiplicative.  (Local copy: the shared `Work.FITop3.Witness` proof pulls in a
large dependency cone that this file does not want.) -/
private lemma gnorm_mul_r6 (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `Im(z̄₁z₂) = r₁s₂ - r₂s₁` in coordinates. -/
private lemma star_mul_im_r6 (z1 z2 : GaussianInt) :
    (((star z1 * z2).im : ℤ) : ℝ)
      = (z1.re : ℝ) * (z2.im : ℝ) - (z1.im : ℝ) * (z2.re : ℝ) := by
  have h : (star z1 * z2).im = z1.re * z2.im - z1.im * z2.re := by
    simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
    ring
  rw [h]; push_cast; ring

/-- `logFac6 z₁ z₂ = log(8√|z₁z₂|/|Δ|)` is half the logarithm of `64/(1-γ²)`, where
`γ = Re(z̄₁z₂)/(|z₁||z₂|)` is the cosine of (7.1).  The content is the ellipse identity
`1 - γ² = Δ²/(|z₁|²|z₂|²)` together with `log(x²) = 2log x`. -/
theorem logFac6_eq_half_log (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    Work.FITop4.logFac6 z1 z2
      = (1 / 2) * Real.log (64 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) := by
  have hre : (((star z1 * z2).re : ℤ) : ℝ)
      = (z1.re : ℝ) * (z2.re : ℝ) + (z1.im : ℝ) * (z2.im : ℝ) :=
    star_mul_re_real z1 z2
  have him : (((star z1 * z2).im : ℤ) : ℝ)
      = (z1.re : ℝ) * (z2.im : ℝ) - (z1.im : ℝ) * (z2.re : ℝ) :=
    star_mul_im_r6 z1 z2
  have hG1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) = (z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2 :=
    gnorm_cast_sq_real z1
  have hG2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) = (z2.re : ℝ) ^ 2 + (z2.im : ℝ) ^ 2 :=
    gnorm_cast_sq_real z2
  have hmul : (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ)
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [gnorm_mul_r6]; push_cast; ring
  set G : ℝ := ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) with hGdef
  set A : ℝ := (((star z1 * z2).re : ℤ) : ℝ) with hAdef
  set B : ℝ := (((star z1 * z2).im : ℤ) : ℝ) with hBdef
  set D : ℝ := ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) with hDdef
  -- the two-squares identity `|z₁z₂|² = Re(z̄₁z₂)² + Im(z̄₁z₂)²`
  have hkey : G = A ^ 2 + B ^ 2 := by
    rw [hGdef, hre, him, hG1, hG2]; ring
  have hDabs : D = |B| := by
    rw [hDdef, hBdef]
    simp only [Work.FIPlan.absDelta, Work.FIPlan.Delta, Nat.cast_natAbs, Int.cast_abs]
  have hBne : B ≠ 0 := by
    intro hB0
    have hD0 : D = 0 := by rw [hDabs, hB0, abs_zero]
    have hcast : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) = 0 := by rw [← hDdef]; exact hD0
    exact hΔ (by exact_mod_cast hcast)
  have hGpos : 0 < G := by
    have h1 : 0 < B ^ 2 := sq_pos_of_ne_zero hBne
    nlinarith [hkey, sq_nonneg A]
  have hGne : G ≠ 0 := ne_of_gt hGpos
  have hDne : D ≠ 0 := by rw [hDabs]; exact abs_ne_zero.mpr hBne
  have hgam : Work.FIArea2.gamOf z1 z2 = A / Real.sqrt G := by
    unfold Work.FIArea2.gamOf
    rw [← hAdef, ← hGdef]
  have hDsq : D ^ 2 = B ^ 2 := by rw [hDabs]; exact sq_abs B
  have h1g : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 = D ^ 2 / G := by
    rw [hgam, div_pow, Real.sq_sqrt (le_of_lt hGpos), hDsq]
    field_simp
    linarith [hkey]
  have h64 : 64 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) = (8 * Real.sqrt G / D) ^ 2 := by
    rw [h1g, div_pow, mul_pow, Real.sq_sqrt (le_of_lt hGpos)]
    field_simp
    ring
  have hlogFac : Work.FITop4.logFac6 z1 z2 = Real.log (8 * Real.sqrt G / D) := by
    unfold Work.FITop4.logFac6
    rw [hmul, ← hDdef]
  rw [hlogFac, h64, Real.log_pow]
  ring

end Work.FIArea2.R6
