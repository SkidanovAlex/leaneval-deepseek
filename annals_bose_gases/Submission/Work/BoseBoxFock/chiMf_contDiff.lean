import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem chiMf_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ g x) := by
  have hchi : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).of_le (by simp))
  have hmf : ContDiff ℝ 1 (Work.BoseBoxFock.mf ℓ g) := by
    have h : Work.BoseBoxFock.mf ℓ g
        = fun x => g x - (((ℓ ^ 3)⁻¹ : ℝ) * ∫ y in Work.BoseK15.corpusBox.boxL ℓ, g y) := rfl
    rw [h]
    exact hg.sub contDiff_const
  exact hchi.mul hmf

end Work.BoseBoxFock
