import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

open MeasureTheory MeasureTheory.Measure ENNReal Real Module Metric
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.InnerProductSpace

theorem unitBall_volume_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    0 < ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1)) := by
  -- The volume of the unit closed ball in a finite-dimensional real inner product
  -- space is given by the closed formula
  --   volume (closedBall 0 1) = ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1))
  have hformula :
      MeasureTheory.volume (Metric.closedBall (0 : E) 1) =
        ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E / Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1)) := by
    rw [InnerProductSpace.volume_closedBall (0 : E) 1]
    simp [one_pow]
  rw [hformula]
  -- The argument of `ofReal` is a positive real number, since the space is nontrivial.
  have hA : 0 < √Real.pi ^ Module.finrank ℝ E / Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
    have hsqrt : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hpow : 0 < √Real.pi ^ Module.finrank ℝ E := pow_pos hsqrt _
    have hGamma : 0 < Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
      apply Real.Gamma_pos_of_pos
      have hfin0 : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
        exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
      positivity
    exact div_pos hpow hGamma
  rw [ENNReal.toReal_ofReal (le_of_lt hA)]
  exact hA

end Commons.Analysis.InnerProductSpace