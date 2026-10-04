import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open MeasureTheory

/-- A function on `Fin n → ℝ` that is continuous on an open bounded set `W`, vanishes outside
`W`, and is globally bounded, is Lebesgue integrable. Indeed its support is contained in the
bounded set `W`, which has finite volume, and on `W` it is bounded (even everywhere) and
(almost everywhere) strongly measurable because it is continuous there. -/
theorem integrable_of_continuousOn_of_bound
    {n : ℕ} {W : Set (Fin n → ℝ)} (hW : IsOpen W) (hbdd : Bornology.IsBounded W)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f W) (h0 : ∀ z ∉ W, f z = 0)
    {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  -- `W` is bounded in the proper space `Fin n → ℝ`, hence has finite volume.
  have hfin : volume W < ⊤ := hbdd.measure_lt_top
  -- `f` is continuous on `W`, so it is (a.e.) strongly measurable for `volume.restrict W`.
  have hmeas : AEStronglyMeasurable f (volume.restrict W) :=
    hf.aestronglyMeasurable hW.measurableSet
  -- Boundedness plus finiteness of the restricted measure gives integrability on `W`,
  -- and `f` vanishes off `W`, so it is integrable on the whole space.
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero
    (IntegrableOn.of_bound hfin hmeas C (Filter.Eventually.of_forall hC)) h0

end Work.Diff.STE.B3
