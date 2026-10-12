import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.C.integrable_partialDeriv_chiScale_sub_smul`

The sliding integrand of the `χ`-localisation is integrable: for `0 < a`, a centre `x` and a
direction `k`,

    `u ↦ (fderiv ℝ (chiScale a) (x - a • u) (kcStdBasis k))²`  is `Integrable`.

Since `chiScale a = χ((a⁻¹) • ·)` with `χ` a smooth bump of compact support
(`Submission.BoseGases.chi_contDiff`, `chi_hasCompactSupport`), the partial derivative
`y ↦ fderiv ℝ (chiScale a) y v` is continuous (`ContDiff.continuous_fderiv`) with compact
support (`HasCompactSupport.fderiv_apply`); its square is therefore continuous with compact
support, hence integrable on `ℝ³`.  Integrability is preserved by the affine substitution
`u ↦ x - a • u`: the reflection/translation `w ↦ x - w` preserves Lebesgue measure
(`Integrable.comp_sub_left`) and the dilation `u ↦ a • u` only rescales it
(`Integrable.comp_smul`).
-/

noncomputable section

open MeasureTheory

namespace Work.UBBInputs9.C

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem integrable_partialDeriv_chiScale_sub_smul (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (fderiv ℝ (Submission.BoseGases.chiScale a) (x - a • u)
        (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hcd := Submission.BoseGases.chiScale_contDiff ha'
  -- the partial derivative `y ↦ fderiv (chiScale a) y v` is continuous ...
  have hcont : Continuous (fun y : ℝ³ =>
      fderiv ℝ (Submission.BoseGases.chiScale a) y (Submission.BoseGases.kcStdBasis k)) :=
    (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
  -- ... and has compact support (the fderiv of a compactly supported function does) ...
  have hcpt : HasCompactSupport (fun y : ℝ³ =>
      (fderiv ℝ (Submission.BoseGases.chiScale a) y (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
    ((Submission.BoseGases.chiScale_hasCompactSupport ha').fderiv_apply ℝ
      (Submission.BoseGases.kcStdBasis k)).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  -- ... hence its square is integrable on `ℝ³`.
  have hG : Integrable (fun y : ℝ³ =>
      (fderiv ℝ (Submission.BoseGases.chiScale a) y (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcpt
  -- Push the integrand through the affine substitution `u ↦ x - a • u`.
  exact (hG.comp_sub_left x).comp_smul ha'

end Work.UBBInputs9.C
