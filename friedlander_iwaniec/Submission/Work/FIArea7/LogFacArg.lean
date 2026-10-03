/-
# `Submission.Work.FIArea7.LogFacArg` — the analytic bridge `logFac = log(2/|sin t|)`

The Fourier expansion of the logarithmic factor of *FI* §16/§17 (`LogFacFourier.lean`) reduces
`Work.FITop3.logFac z₁ z₂` to the log-sine series via the two elementary facts

  `logFac z₁ z₂ = log (2 / |sin(arg z₂ − arg z₁)|)`,   `|Δ(z₁,z₂)| = |z₁||z₂|·|sin(arg z₂ − arg z₁)|`.

This module carries those facts (and the Gaussian-integer facts they rest on) under its own names,
so that the §17 Fourier bridge does not depend on the round-3 structural module `area7_r3`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.VcutMod_le_pair_crude

set_option autoImplicit false

namespace Work.FIArea7

namespace LogFacArg

noncomputable section

/-- A nonzero Gaussian integer has positive norm. -/
lemma gnorm_pos_of_ne_zero {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm]
  exact Int.natAbs_pos.mpr (ne_of_gt ((GaussianInt.norm_pos).mpr hz))

/-- The coercion `ℤ[i] → ℂ` does not vanish on a positive-norm element. -/
lemma toComplex_ne_zero_of_gnorm_pos {z : GaussianInt} (h : 0 < Work.FIPlan.gnorm z) :
    (z : ℂ) ≠ 0 := by
  intro h0
  have hre : z.re = 0 := by
    have h1 := congrArg Complex.re h0
    have h2 : ((z.re : ℤ) : ℝ) = 0 := by simpa using h1
    exact_mod_cast h2
  have him : z.im = 0 := by
    have h1 := congrArg Complex.im h0
    have h2 : ((z.im : ℤ) : ℝ) = 0 := by simpa using h1
    exact_mod_cast h2
  have hz : z = 0 := by ext <;> simp [hre, him]
  rw [hz] at h
  simp [Work.FIPlan.gnorm] at h

/-- `Δ(z₁,z₂) = Im(z̄₁z₂)`, read in `ℂ`. -/
lemma Delta_toComplex (z1 z2 : GaussianInt) :
    (star (z1 : ℂ) * (z2 : ℂ)).im = ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) := by
  have h : (((star z1 * z2 : GaussianInt) : ℂ)) = star (z1 : ℂ) * (z2 : ℂ) := by
    rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star]; simp
  rw [Work.FIPlan.Delta, ← h, GaussianInt.intCast_im]

/-- The normalising factor `|z₁||z₂|` of the angular-difference identities does not vanish when
`Δ(z₁,z₂) ≠ 0`. -/
lemma norm_mul_ne_zero_of_delta_ne_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ ≠ 0 := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  exact mul_ne_zero
    (norm_ne_zero_iff.mpr (toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)))
    (norm_ne_zero_iff.mpr (toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)))

/-- **The sine of the difference of the arguments**: for `Δ(z₁,z₂) ≠ 0`,
`sin(arg z₂ − arg z₁) = Δ/|z₁||z₂|`. -/
lemma sin_arg_sub {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)
      = ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) / (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖) := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hc1 : (z1 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)
  have hc2 : (z2 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)
  have hn : ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hc1) (norm_ne_zero_iff.mpr hc2)
  rw [Real.sin_sub, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg hc2, Complex.cos_arg hc1,
    ← Delta_toComplex]
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- **`Δ` in terms of the norms and the sine**: `|Δ(z₁,z₂)| = |z₁||z₂|·|sin(arg z₂ − arg z₁)|`. -/
lemma absDelta_eq_norm_mul_abs_sin {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hc1 : (z1 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)
  have hc2 : (z2 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)
  have hN : 0 < ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ :=
    mul_pos (norm_pos_iff.mpr hc1) (norm_pos_iff.mpr hc2)
  rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs, sin_arg_sub h, abs_div,
    abs_of_pos hN]
  field_simp

/-- **The logarithmic factor as a function of the angular difference**: for `Δ ≠ 0`,
`logFac z₁ z₂ = log (2 / |sin(arg z₂ − arg z₁)|)`. -/
lemma logFac_eq_arg {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Work.FITop3.logFac z1 z2 = Real.log (2 / |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)|) := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hc1 : (z1 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)
  have hc2 : (z2 : ℂ) ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)
  have hN : ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hc1) (norm_ne_zero_iff.mpr hc2)
  have hsq : Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by
    rw [← Work.FIArea4.crude_norm_toComplex_eq_sqrt (z1 * z2), GaussianInt.toComplex_mul,
      norm_mul]
  have habs := absDelta_eq_norm_mul_abs_sin (z1 := z1) (z2 := z2) h
  rw [Work.FITop3.logFac, hsq, habs]
  congr 1
  field_simp

end

end LogFacArg

end Work.FIArea7
