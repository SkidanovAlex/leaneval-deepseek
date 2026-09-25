import Mathlib
import Submission.Work.NN.Assemble.L2Forms

namespace Work.NN.Assemble

open MeasureTheory Set

/-- **The cylinder over a circle in `ℂⁿ = Fin n → ℂ` is Lebesgue-null.**  For every coordinate `j` and every radius `r`, the set of `z` with `‖z j‖ = r` has measure zero.  (Suggested route: `volume` on `Fin n → ℂ` is the product `Measure.pi (fun _ => volume_ℂ)` [instance `MeasureTheory.MeasureSpace.pi`], so `Measure.pi_pi` reduces to the measure of the circle in `ℂ`, which is zero because `volume` on `ℂ = ℝ × ℝ` is the product measure and every vertical section of the circle is a finite set.) -/
theorem coordSphere_volume_eq_zero {n : ℕ} (j : Fin n) (r : ℝ) :
    MeasureTheory.volume {z : Fin n → ℂ | ‖z j‖ = r} = 0 := by
  -- The set is a cylinder `Set.pi univ` whose `j`-th factor is the circle `Metric.sphere 0 r`.
  have hset : {z : Fin n → ℂ | ‖z j‖ = r}
      = Set.pi Set.univ (fun i : Fin n =>
          if i = j then Metric.sphere (0 : ℂ) r else Set.univ) := by
    ext z; simp
  -- `volume` on `Fin n → ℂ` is the product of the coordinate Lebesgue measures.
  rw [hset, volume_pi_pi]
  -- The `j`-th factor is the circle in `ℂ`, which is Haar-null.
  have hsphere : (MeasureTheory.volume : Measure ℂ) (Metric.sphere (0 : ℂ) r) = 0 :=
    MeasureTheory.Measure.addHaar_sphere (MeasureTheory.volume : Measure ℂ) 0 r
  -- A product with one zero factor vanishes.
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hsphere])

end Work.NN.Assemble
