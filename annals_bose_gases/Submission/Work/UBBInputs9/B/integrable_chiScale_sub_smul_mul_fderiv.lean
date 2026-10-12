import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integrable_chiScale_sub_smul_mul_fderiv`

The sliding integrand of the `χ`-localisation, multiplied by its own Fréchet derivative along a
fixed direction, is integrable: for `0 < a`, a centre `c` and a direction `e`,

    `u ↦ chiScale a (c - a • u) * fderiv ℝ (chiScale a) (c - a • u) e`  is `Integrable`.

Since `chiScale a = χ((a⁻¹) • ·)` with `χ` a smooth bump of compact support
(`Submission.BoseGases.chi_contDiff`, `chi_hasCompactSupport`), the function

    `G y := chiScale a y * fderiv ℝ (chiScale a) y e`

is continuous (`ContDiff.continuous_fderiv`) and has compact support contained in that of
`chiScale a` (`Submission.BoseGases.chiScale_hasCompactSupport`), hence is integrable on `ℝ³`.
Integrability is preserved by the affine substitution `u ↦ c - a • u`: the reflection/translation
`w ↦ c - w` preserves Lebesgue measure (`Integrable.comp_sub_left`) and the dilation `u ↦ a • u`
only rescales it (`Integrable.comp_smul`).
-/

noncomputable section

open MeasureTheory

namespace Work.UBBInputs9.B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem integrable_chiScale_sub_smul_mul_fderiv (a : ℝ) (ha : 0 < a)
    (c e : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale a (c - a • u) *
        fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hcd := Submission.BoseGases.chiScale_contDiff ha'
  -- the product `chiScale a · (∂_e chiScale a)` is continuous ...
  have hcont : Continuous (fun y : ℝ³ =>
      Submission.BoseGases.chiScale a y *
        fderiv ℝ (Submission.BoseGases.chiScale a) y e) :=
    hcd.continuous.mul ((hcd.continuous_fderiv (by simp)).clm_apply continuous_const)
  -- ... and has compact support, being supported in that of `chiScale a` ...
  have hcs : HasCompactSupport (fun y : ℝ³ =>
      Submission.BoseGases.chiScale a y *
        fderiv ℝ (Submission.BoseGases.chiScale a) y e) :=
    (Submission.BoseGases.chiScale_hasCompactSupport ha').mono
      (Function.support_mul_subset_left _ _)
  -- ... hence is integrable on `ℝ³`.
  have hG : Integrable (fun y : ℝ³ =>
      Submission.BoseGases.chiScale a y *
        fderiv ℝ (Submission.BoseGases.chiScale a) y e) :=
    hcont.integrable_of_hasCompactSupport hcs
  -- Push the integrand through the affine substitution `u ↦ c - a • u`.
  exact (hG.comp_sub_left c).comp_smul ha'

end Work.UBBInputs9.B
