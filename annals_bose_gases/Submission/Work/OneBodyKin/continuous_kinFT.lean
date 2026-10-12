import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

open MeasureTheory
open scoped Topology

/-- The `p`-convention Fourier transform of an `L¹` function is continuous. -/
theorem continuous_kinFT {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : MeasureTheory.Integrable g) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT g p) := by
  have h : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∫ y : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y) := by
    apply continuous_of_dominated (bound := fun y => ‖g y‖)
    · intro p
      have hc : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) := by fun_prop
      exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
    · intro p
      filter_upwards with y
      rw [norm_mul, Complex.norm_exp]
      have hz : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hz, Real.exp_zero, one_mul]
    · exact hg.norm
    · filter_upwards with y
      fun_prop
  simpa [Submission.BoseGases.kinFT] using h

end Work.OneBodyKin
