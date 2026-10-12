import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

/-- The lattice plane wave `x ↦ e^{i⟪κ,x⟫}` has modulus one everywhere. -/
lemma norm_latWave (κ x : EuclideanSpace ℝ (Fin 3)) : ‖latWave κ x‖ = 1 := by
  simp [latWave, Complex.norm_exp]

/-- The lattice plane wave is continuous (indeed `C^∞`). -/
lemma continuous_latWave (κ : EuclideanSpace ℝ (Fin 3)) : Continuous (latWave κ) :=
  (latWave_contDiff κ).continuous

/-- **Integrability of `W · e^{i⟪κ,·⟫}` for `L¹` weights `W`.**
Since the plane wave has modulus one, multiplication by it preserves `L¹`: this is the
integrability input of the Fourier-form identity `integral_mul_latWave_eq_conj_kinFT`. -/
theorem integrable_mul_latWave {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (κ : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun x => (W x : ℂ) * Work.BoseBoxFock.L1Tails.latWave κ x) := by
  refine hWi.ofReal.mul_bdd (c := 1) ?_ ?_
  · exact (continuous_latWave κ).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_latWave κ x]

end Work.BoseBoxFock.L1Tails
