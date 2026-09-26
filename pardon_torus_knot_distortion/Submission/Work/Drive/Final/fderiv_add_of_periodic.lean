import Mathlib

namespace Work.Drive.Final

/-- If `F : ℝ × ℝ → E` is invariant under translation by `c` (i.e. `F (y + c) = F y` for all `y`),
then `fderiv ℝ F` is invariant under the same translation.

Proof: precomposing with the translation `y ↦ y + c` multiplies (on the right) the derivative at `x`
with the derivative of the translation, which is the identity; and since the translate of `F` is `F`
itself, this says `fderiv ℝ F x = fderiv ℝ F (x + c)`. -/
theorem fderiv_add_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {c : ℝ × ℝ} (h : ∀ x : ℝ × ℝ, F (x + c) = F x) (x : ℝ × ℝ) :
    fderiv ℝ F (x + c) = fderiv ℝ F x := by
  have h1 : (fun y : ℝ × ℝ => F (y + c)) = F := funext h
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) c
  rw [h1] at h2
  exact h2.symm

end Work.Drive.Final
