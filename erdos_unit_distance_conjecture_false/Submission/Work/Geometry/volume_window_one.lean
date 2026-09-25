import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- The volume of the unit window `B_1` in the mixed space of a totally complex number field:
for such a field the mixed space is a product of `nrComplexPlaces K` copies of `ℂ`, each
contributing a disc of radius `1` of area `π`. -/
theorem volume_window_one (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    volume (Window K 1) =
      ENNReal.ofReal ((Real.pi : ℝ) ^ (InfinitePlace.nrComplexPlaces K)) := by
  rw [← convexBodyLT_eq_window (K := K) (fun _ => 1) (fun w => NNReal.coe_one)]
  rw [mixedEmbedding.convexBodyLT_volume]
  have hprod : (∏ w : InfinitePlace K, ((fun _ => 1 : InfinitePlace K → NNReal) w) ^ w.mult) = 1 := by
    simp only [one_pow, Finset.prod_const_one]
  rw [hprod, ENNReal.coe_one, mul_one]
  have hfac : mixedEmbedding.convexBodyLTFactor K = NNReal.pi ^ InfinitePlace.nrComplexPlaces K := by
    rw [mixedEmbedding.convexBodyLTFactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
      pow_zero, one_mul]
  rw [hfac, ENNReal.coe_pow, ENNReal.ofReal_pow Real.pi_nonneg]
  congr 1
  rw [show (Real.pi : ℝ) = ((NNReal.pi : NNReal) : ℝ) from rfl, ENNReal.ofReal_coe_nnreal]

end Work.Geometry
