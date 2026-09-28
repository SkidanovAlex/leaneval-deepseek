import Mathlib
import Submission.Work.HP.Defs

/-!
# The volume of the unit ball is intrinsic

For a finite-dimensional real inner product space `V`, the Lebesgue (`volume`) measure of the
closed unit ball of `V` is the same as that of the closed unit ball of the standard Euclidean
space `EuclideanSpace ℝ (Fin (finrank ℝ V))`: the `volume` on an inner product space is the Haar
measure normalised by an orthonormal basis, and any orthonormal basis gives a linear isometry
equivalence with `EuclideanSpace ℝ (Fin (finrank ℝ V))`, which maps the unit ball to the unit
ball and preserves `volume` (`OrthonormalBasis.measurePreserving_repr_symm`).

Consequently, `ballVol (finrank ℝ V)` — defined as the volume of the unit ball of
`EuclideanSpace ℝ (Fin (finrank ℝ V))` — computes the unit ball volume of *any*
finite-dimensional real inner product space, without any `Nontrivial` assumption: in dimension
`0` both sides are the mass `1` of the (Dirac) measure on the one-point space, and the transport
argument covers that case as well.
-/

namespace Work.HP

open MeasureTheory

/-- The `volume` of the closed unit ball of a finite-dimensional real inner product space equals
the `volume` of the closed unit ball of the standard Euclidean space of the same dimension. -/
theorem volume_closedBall_unit_eq_euclid {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :
    volume (Metric.closedBall (0 : V) 1) =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) 1) := by
  -- `repr.symm` is a linear isometry equivalence from the standard Euclidean space onto `V`
  -- (this works in dimension `0` too), and it is volume preserving.
  have hmp := (stdOrthonormalBasis ℝ V).measurePreserving_repr_symm
  have hpre : (⇑(stdOrthonormalBasis ℝ V).repr.symm) ⁻¹' (Metric.closedBall (0 : V) 1) =
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) 1) := by
    rw [LinearIsometryEquiv.preimage_closedBall]
    simp
  rw [← hpre, hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet]

theorem BallVolIntrinsic {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :
    (MeasureTheory.volume (Metric.closedBall 0 1 : Set V)).toReal =
      ballVol (Module.finrank ℝ V) := by
  rw [volume_closedBall_unit_eq_euclid]
  rfl

end Work.HP
