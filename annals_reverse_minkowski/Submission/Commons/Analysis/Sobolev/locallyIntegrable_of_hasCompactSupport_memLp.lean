import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Sobolev

/-- If `f : E → F` is in `L^p` (`p ≥ 1`) with respect to Lebesgue measure on a
finite-dimensional real inner product space `E`, and `f` has compact support, then
`f` is locally integrable.

This is an immediate consequence of `MeasureTheory.MemLp.locallyIntegrable`: Lebesgue
measure on a finite-dimensional real inner product space is a locally finite measure,
and `L^p ⊆ L^1_loc` for `p ≥ 1`. The compact-support hypothesis is not needed for the
conclusion but is part of the requested interface. -/
theorem locallyIntegrable_of_hasCompactSupport_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] {f : E → F} {p : ℝ} (hp : 1 ≤ p) (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume) (hfc : HasCompactSupport f) : MeasureTheory.LocallyIntegrable f MeasureTheory.volume := by
  exact hf.locallyIntegrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp)

end Commons.Analysis.Sobolev