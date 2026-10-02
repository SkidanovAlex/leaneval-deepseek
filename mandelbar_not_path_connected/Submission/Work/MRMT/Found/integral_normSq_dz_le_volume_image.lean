import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter Topology
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- **Area bound for the `∂`-energy of a homeomorphism with bounded dilatation (general set).**

If `F : ℂ ≃ₜ ℂ` is a `C¹` homeomorphism whose complex dilatation is pointwise bounded by
`k < 1` (`∂̄F = μF · ∂F` with `‖μF‖ ≤ k`), then for every compact `L ⊆ ℂ` the `L²` norm of
`∂F` over `L` is controlled by the area of the image:
`∫_L ‖∂F‖² ≤ (1-k²)⁻¹ · area (F '' L)`.

This is the general-set version of `Work.MRMT.Found.dzSq_integral_le_area` (which is stated
for balls); the proof uses Mathlib's change-of-variables formula
`lintegral_abs_det_fderiv_eq_addHaar_image` on the (measurable, compact) set `L`, the
algebraic identity `det DF = ‖∂F‖² - ‖∂̄F‖²`, and the finiteness of the volume of the compact
image `F '' L`. -/
theorem integral_normSq_dz_le_volume_image {F : ℂ ≃ₜ ℂ} {μF : ℂ → ℂ} {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    (hrel : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hμ : ∀ z : ℂ, ‖μF z‖ ≤ k) {L : Set ℂ} (hL : IsCompact L) :
    ∫ z in L, ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2 ≤
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (F '' L)).toReal / (1 - k ^ 2) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith [sq_nonneg k]
  have ha : 0 ≤ (1 - k ^ 2)⁻¹ := inv_nonneg.mpr hk2.le
  -- pointwise distortion inequality from the Beltrami relation
  have hdil : ∀ z : ℂ, ‖Work.MRMT.dzbar (F : ℂ → ℂ) z‖ ≤ k * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ := by
    intro z
    rw [hrel z, norm_mul]
    exact mul_le_mul_of_nonneg_right (hμ z) (norm_nonneg _)
  -- pointwise `ENNReal` distortion estimates
  have hpt : ∀ z : ℂ,
      ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2) ≤
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| ∧
      ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| ≤
        ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2) := by
    intro z
    have hdet := Sobolev.det_fderiv_eq (F : ℂ → ℂ) z
    have hn2 : ‖Work.MRMT.dzbar (F : ℂ → ℂ) z‖ ^ 2 ≤
        k ^ 2 * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2 := by
      calc ‖Work.MRMT.dzbar (F : ℂ → ℂ) z‖ ^ 2 ≤ (k * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hdil z) 2
        _ = k ^ 2 * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2 := by ring
    have hmain : (1 - k ^ 2) * ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2 ≤
        (fderiv ℝ (F : ℂ → ℂ) z).det := by
      rw [hdet]; nlinarith [hn2]
    have hdetnn : 0 ≤ (fderiv ℝ (F : ℂ → ℂ) z).det :=
      le_trans (mul_nonneg hk2.le (sq_nonneg _)) hmain
    refine ⟨?_, ?_⟩
    · have hineq : ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2 ≤
          (1 - k ^ 2)⁻¹ * |(fderiv ℝ (F : ℂ → ℂ) z).det| := by
        rw [abs_of_nonneg hdetnn]
        exact (le_inv_mul_iff₀ hk2).2 hmain
      calc ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2)
          ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹ * |(fderiv ℝ (F : ℂ → ℂ) z).det|) :=
            ENNReal.ofReal_le_ofReal hineq
        _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| :=
            ENNReal.ofReal_mul ha
    · rw [abs_of_nonneg hdetnn]
      exact ENNReal.ofReal_le_ofReal
        (by rw [hdet]; nlinarith [sq_nonneg ‖Work.MRMT.dzbar (F : ℂ → ℂ) z‖])
  have hdiff : ∀ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z := fun z =>
    (hF.contDiffAt (x := z)).differentiableAt (by norm_num)
  have hLmeas : MeasurableSet L := hL.isClosed.measurableSet
  -- change of variables: `∫_L |det DF| = area (F '' L)`
  have hcov : ∫⁻ x in L, ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) x).det| =
      (volume : Measure ℂ) (F '' L) :=
    lintegral_abs_det_fderiv_eq_addHaar_image (f := (F : ℂ → ℂ))
      (f' := fun z => fderiv ℝ (F : ℂ → ℂ) z) volume
      hLmeas (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) F.injective.injOn
  have hlin : ∫⁻ z in L, ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2) ≤
      ENNReal.ofReal ((1 - k ^ 2)⁻¹) * (volume : Measure ℂ) (F '' L) := by
    have h1 : ∫⁻ z in L, ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2) ≤
        ∫⁻ z in L, ENNReal.ofReal ((1 - k ^ 2)⁻¹) *
          ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| :=
      setLIntegral_mono_ae' hLmeas (Eventually.of_forall fun z _ => (hpt z).1)
    have h2 : ∫⁻ z in L, ENNReal.ofReal ((1 - k ^ 2)⁻¹) *
          ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| =
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) *
          ∫⁻ z in L, ENNReal.ofReal |(fderiv ℝ (F : ℂ → ℂ) z).det| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [h2, hcov] at h1
    exact h1
  have hfd : Continuous (fderiv ℝ (F : ℂ → ℂ)) := hF.continuous_fderiv (by norm_num)
  have hdzc : Continuous (fun z : ℂ => Work.MRMT.dz (F : ℂ → ℂ) z) := by
    simp only [Work.MRMT.dz]
    exact ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  have hcont : Continuous (fun z : ℂ => ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2) := (hdzc.norm).pow 2
  have hbool : ∫ z in L, ‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2
      = (∫⁻ z in L, ENNReal.ofReal (‖Work.MRMT.dz (F : ℂ → ℂ) z‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _)
      hcont.aestronglyMeasurable
  have hfin : (volume : Measure ℂ) (F '' L) ≠ ⊤ := (hL.image F.continuous).measure_lt_top.ne
  rw [hbool, div_eq_inv_mul]
  have hR : (ENNReal.ofReal ((1 - k ^ 2)⁻¹) * (volume : Measure ℂ) (F '' L)).toReal
      = (1 - k ^ 2)⁻¹ * ((volume : Measure ℂ) (F '' L)).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  rw [← hR]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlin

end Work.MRMT.Found
