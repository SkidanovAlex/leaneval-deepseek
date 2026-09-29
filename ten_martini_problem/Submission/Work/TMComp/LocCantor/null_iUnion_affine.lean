import Mathlib

namespace Work.TMComp.LocCantor

/-- A countable union of images of a null set `Y` under affine maps is null.

The index set `ℤ × ℤ × Bool` is countable, and each affine map `y ↦ a * y + b` is
differentiable on all of `ℝ`, hence maps the null set `Y` to a null set by
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`. -/
theorem null_iUnion_affine {Y : Set ℝ} (hY : MeasureTheory.volume Y = 0) (F : ℤ × ℤ × Bool → ℝ × ℝ) :
    MeasureTheory.volume (⋃ p : ℤ × ℤ × Bool, (fun y => (F p).1 * y + (F p).2) '' Y) = 0 := by
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro p
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    MeasureTheory.volume (by fun_prop) hY

end Work.TMComp.LocCantor
