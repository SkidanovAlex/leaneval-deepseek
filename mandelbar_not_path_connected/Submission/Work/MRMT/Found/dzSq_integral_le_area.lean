import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

set_option linter.unusedVariables false

namespace Work.MRMT.Found

/-- **Pointwise distortion estimates.**  If `‖∂̄F z‖ ≤ k ‖∂F z‖` with `0 ≤ k < 1`, then at every
point `z` the Jacobian determinant of `F` is non-negative, is dominated by `‖∂F z‖²`, and
controls `‖∂F z‖²` through `(1-k²) ‖∂F z‖² ≤ det DF z`.  Phrased with `ENNReal.ofReal` so that
it can be fed into `∫⁻`. -/
private lemma ofReal_dzSq_pointwise {F : ℂ → ℂ} {k : ℝ} (hk2 : 0 < 1 - k ^ 2)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖) (z : ℂ) :
    ENNReal.ofReal (‖dz F z‖ ^ 2) ≤
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ F z).det| ∧
      ENNReal.ofReal |(fderiv ℝ F z).det| ≤ ENNReal.ofReal (‖dz F z‖ ^ 2) := by
  have hdet := Sobolev.det_fderiv_eq F z
  have hn2 : ‖dzbar F z‖ ^ 2 ≤ k ^ 2 * ‖dz F z‖ ^ 2 := by
    calc ‖dzbar F z‖ ^ 2 ≤ (k * ‖dz F z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdil z) 2
      _ = k ^ 2 * ‖dz F z‖ ^ 2 := by ring
  have hmain : (1 - k ^ 2) * ‖dz F z‖ ^ 2 ≤ (fderiv ℝ F z).det := by
    rw [hdet]; nlinarith [hn2]
  have hdetnn : 0 ≤ (fderiv ℝ F z).det :=
    le_trans (mul_nonneg hk2.le (sq_nonneg _)) hmain
  refine ⟨?_, ?_⟩
  · have hineq : ‖dz F z‖ ^ 2 ≤ (1 - k ^ 2)⁻¹ * |(fderiv ℝ F z).det| := by
      rw [abs_of_nonneg hdetnn]
      exact (le_inv_mul_iff₀ hk2).2 hmain
    calc ENNReal.ofReal (‖dz F z‖ ^ 2)
        ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹ * |(fderiv ℝ F z).det|) := ENNReal.ofReal_le_ofReal hineq
      _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ F z).det| :=
          ENNReal.ofReal_mul (inv_nonneg.mpr hk2.le)
  · rw [abs_of_nonneg hdetnn]
    exact ENNReal.ofReal_le_ofReal (by rw [hdet]; nlinarith [sq_nonneg ‖dzbar F z‖])

/-- **Area bound for the `∂`-energy of a quasiconformal (with respect to the pointwise
distortion inequality) map.**  For a `C¹` injective map `F : ℂ → ℂ` whose complex dilatation is
bounded by `k < 1` pointwise (`‖∂̄F z‖ ≤ k ‖∂F z‖`), the `L²` norm of `∂F` over a ball is
controlled by the area of the image of that ball:
`∫_B ‖∂F‖² ≤ (1-k²)⁻¹ · area (F '' B)`.

The proof combines

* the algebraic identity `det DF = ‖∂F‖² - ‖∂̄F‖²` (`Work.MRMT.Sobolev.det_fderiv_eq`), which with
  the pointwise dilation hypothesis gives `‖∂F z‖² ≤ (1-k²)⁻¹ |det DF z|` and
  `|det DF z| ≤ ‖∂F z‖²`;
* Mathlib's change of variables formula `lintegral_abs_det_fderiv_eq_addHaar_image`, applied to
  the ball `B` (where `F` is differentiable because it is `C¹` and injective by hypothesis);
* the conversion of the Bochner integral of the non-negative function `‖∂F‖²` into the `toReal`
  of its `lintegral`. -/
theorem dzSq_integral_le_area {F : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hF : ContDiff ℝ 1 F) (hinj : Function.Injective F)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in Metric.ball c R, ‖dz F z‖ ^ 2 ≤ (1 - k ^ 2)⁻¹ *
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (F '' Metric.ball c R)).toReal := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith [sq_nonneg k]
  have ha : 0 ≤ (1 - k ^ 2)⁻¹ := inv_nonneg.mpr hk2.le
  have hpt : ∀ z : ℂ, ENNReal.ofReal (‖dz F z‖ ^ 2) ≤
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ F z).det| ∧
      ENNReal.ofReal |(fderiv ℝ F z).det| ≤ ENNReal.ofReal (‖dz F z‖ ^ 2) :=
    fun z => ofReal_dzSq_pointwise hk2 hdil z
  -- `F` is differentiable everywhere
  have hdiff : ∀ z : ℂ, DifferentiableAt ℝ F z := fun z =>
    (hF.contDiffAt (x := z)).differentiableAt (by norm_num)
  set B : Set ℂ := Metric.ball c R with hBdef
  have hBmeas : MeasurableSet B := by rw [hBdef]; exact Metric.isOpen_ball.measurableSet
  -- change of variables: the integral of `|det DF|` over `B` is the area of `F '' B`
  have hcov : ∫⁻ x in B, ENNReal.ofReal |(fderiv ℝ F x).det| = volume (F '' B) :=
    lintegral_abs_det_fderiv_eq_addHaar_image (f := F) (f' := fun z => fderiv ℝ F z) volume
      hBmeas (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn
  have hlin : ∫⁻ z in B, ENNReal.ofReal (‖dz F z‖ ^ 2) ≤
      ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (F '' B) := by
    have h1 : ∫⁻ z in B, ENNReal.ofReal (‖dz F z‖ ^ 2) ≤
        ∫⁻ z in B, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ F z).det| :=
      setLIntegral_mono_ae' hBmeas (Eventually.of_forall fun z _ => (hpt z).1)
    have h2 : ∫⁻ z in B, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ F z).det| =
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ∫⁻ z in B, ENNReal.ofReal |(fderiv ℝ F z).det| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [h2, hcov] at h1
    exact h1
  -- conversely the area of the image is dominated by the `∂`-energy
  have hge : volume (F '' B) ≤ ∫⁻ z in B, ENNReal.ofReal (‖dz F z‖ ^ 2) := by
    rw [← hcov]
    exact setLIntegral_mono_ae' hBmeas (Eventually.of_forall fun z _ => (hpt z).2)
  -- the Bochner integral of the non-negative integrand
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hdzc : Continuous (fun z : ℂ => dz F z) := by
    simp only [dz]
    exact ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  have hcont : Continuous (fun z : ℂ => ‖dz F z‖ ^ 2) := (hdzc.norm).pow 2
  have hbool : ∫ z in B, ‖dz F z‖ ^ 2
      = (∫⁻ z in B, ENNReal.ofReal (‖dz F z‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _)
      hcont.aestronglyMeasurable
  rw [hBdef] at hlin hge hbool ⊢
  rw [hbool]
  by_cases htop : volume (F '' Metric.ball c R) = ⊤
  · -- infinite image: both sides vanish
    have hLtop : ∫⁻ z in Metric.ball c R, ENNReal.ofReal (‖dz F z‖ ^ 2) = ⊤ := by
      rw [htop] at hge
      exact top_le_iff.mp hge
    rw [hLtop, htop, ENNReal.toReal_top]
    simp
  · -- finite image: monotonicity of `toReal`
    have hfin : (ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (F '' Metric.ball c R)).toReal
        = (1 - k ^ 2)⁻¹ * (volume (F '' Metric.ball c R)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
    rw [← hfin]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) hlin

end Work.MRMT.Found
