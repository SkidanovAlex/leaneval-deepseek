import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Resolve

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- For a real number `a`, the squared norm of its image in `ℂ` is `a²`. -/
private lemma norm_sq_ofReal_coe (a : ℝ) : ‖(a : ℂ)‖ ^ 2 = a ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal, pow_two]

/-- The Fréchet derivative of the complexification `y ↦ (v y : ℂ)` of a `C¹` real function `v`
is the complexification of `fderiv ℝ v`: applied to a vector `b` it gives `(fderiv ℝ v x b : ℂ)`. -/
private lemma fderiv_ofReal_coe_apply (v : ℝ³ → ℝ) (hv : ContDiff ℝ 1 v) (x b : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => (v y : ℂ)) x b = ((fderiv ℝ v x b : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := v x)).comp x
      ((hv.differentiable_one x).hasFDerivAt)
  have hd : fderiv ℝ (fun y : ℝ³ => (v y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ v x) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h.fderiv
  rw [hd]
  simp [ContinuousLinearMap.comp_apply]

theorem dirichlet_sum_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (hv : ContDiff ℝ 1 v) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
        ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => (v y : ℂ)) x
          (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          (fderiv ℝ v x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  simp only [fderiv_ofReal_coe_apply v hv, norm_sq_ofReal_coe]

end Work.SmallBoxBridge.Resolve
