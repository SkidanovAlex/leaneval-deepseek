import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.SamplingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Change of variables `ℝ³ ≅ Fin 3 → ℝ` for the Lebesgue integral: `WithLp.toLp 2` is a
volume-preserving measurable equivalence (`PiLp.volume_preserving_toLp`), so pulling a function
back along it does not change the integral. -/
theorem integral_toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ³ → E) :
    ∫ y : ℝ³, F y = ∫ x : Fin 3 → ℝ, F (WithLp.toLp 2 x) := by
  rw [← MeasureTheory.MeasurePreserving.integral_comp'
    (f := MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (PiLp.volume_preserving_toLp (Fin 3)) F]
  rfl

end Work.BoseBoxFock
