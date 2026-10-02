/-
Wirtinger calculus helpers for the MRMT/QC development.

`Work.MRMT.dz` and `Work.MRMT.dzbar` are defined (in `Submission.Work.MRMT.Basic`) from the real
Fréchet derivative as
`dz f z = ((fderiv ℝ f z) 1 - I * (fderiv ℝ f z) I) / 2` and
`dzbar f z = ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I) / 2`.
-/
import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal ComplexConjugate

namespace Work.MRMT.QC

variable {F G : ℂ → ℂ} {z w : ℂ}

/-- Decomposition of a real-linear map `ℂ → ℂ` in terms of its values at `1` and `I`. -/
theorem clm_apply_eq (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = ((L 1 - Complex.I * L Complex.I) / 2) * w
      + ((L 1 + Complex.I * L Complex.I) / 2) * conj w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have h1 : (w.re : ℂ) = (w.re : ℝ) • (1 : ℂ) := by simp [Complex.real_smul]
  have h2 : (w.im : ℂ) * Complex.I = (w.im : ℝ) • (Complex.I : ℂ) := by simp [Complex.real_smul]
  rw [hw, h1, h2, map_add, map_smul, map_smul]
  simp only [Complex.real_smul]
  simp only [map_add, map_mul, map_one]
  rw [Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp only [pow_two, Complex.I_mul_I, Complex.conj_ofReal]
  ring

theorem dz_mul (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    Work.MRMT.dz (fun w => F w * G w) z = Work.MRMT.dz F z * G z + F z * Work.MRMT.dz G z := by
  have h1 : fderiv ℝ (fun w => F w * G w) z = F z • fderiv ℝ G z + G z • fderiv ℝ F z :=
    fderiv_mul hF hG
  simp only [Work.MRMT.dz, h1]
  simp only [add_apply, smul_apply]
  ring

theorem dzbar_mul (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    Work.MRMT.dzbar (fun w => F w * G w) z = Work.MRMT.dzbar F z * G z + F z * Work.MRMT.dzbar G z := by
  have h1 : fderiv ℝ (fun w => F w * G w) z = F z • fderiv ℝ G z + G z • fderiv ℝ F z :=
    fderiv_mul hF hG
  simp only [Work.MRMT.dzbar, h1]
  simp only [add_apply, smul_apply]
  ring

theorem dz_conj (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dz (fun w => conj (F w)) z = conj (Work.MRMT.dzbar F z) := by
  have h1 : fderiv ℝ (fun w => conj (F w)) z
      = ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L fderiv ℝ F z :=
    (hF.hasFDerivAt.star).fderiv
  have hA : (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) 1))
      = conj ((fderiv ℝ F z) 1) := by simp [starL'_apply]
  have hB : (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) Complex.I))
      = conj ((fderiv ℝ F z) Complex.I) := by simp [starL'_apply]
  simp only [Work.MRMT.dz, Work.MRMT.dzbar, h1, ContinuousLinearMap.comp_apply, hA, hB]
  simp only [map_add, map_sub, map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring_nf

theorem dzbar_conj (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dzbar (fun w => conj (F w)) z = conj (Work.MRMT.dz F z) := by
  have h1 : fderiv ℝ (fun w => conj (F w)) z
      = ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L fderiv ℝ F z :=
    (hF.hasFDerivAt.star).fderiv
  have hA : (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) 1))
      = conj ((fderiv ℝ F z) 1) := by simp [starL'_apply]
  have hB : (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) Complex.I))
      = conj ((fderiv ℝ F z) Complex.I) := by simp [starL'_apply]
  simp only [Work.MRMT.dz, Work.MRMT.dzbar, h1, ContinuousLinearMap.comp_apply, hA, hB]
  simp only [map_add, map_sub, map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring_nf

end Work.MRMT.QC
