import Mathlib

namespace Work.Modular

open scoped Manifold Real MatrixGroups
open UpperHalfPlane

/-- The `SL(2, ℤ)`-action on `ℍ` is defined by composing the coefficient action on `ℍ`
with the homomorphism `SL(2, ℤ) →* GL(2, ℝ)`; this makes the two actions agree. -/
lemma S_smul_eq_mapGL_smul (τ : ℍ) :
    ModularGroup.S • τ = (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • τ :=
  MulAction.compHom_smul_def ..

/-- The determinant of the image of any special linear group element in `GL(2, ℝ)` is `1`. -/
lemma mapGL_S_det_pos :
    (0 : ℝ) < (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S).det.val := by
  simp

/-- The modular `S`-action `τ ↦ -1/τ` on the upper half plane is holomorphic: it is given by the
element `ModularGroup.S ∈ SL(2, ℤ)`, whose image in `GL(2, ℝ)` has determinant `1`. -/
lemma mdifferentiable_S_smul : MDiff (fun τ : ℍ => ModularGroup.S • τ) := by
  have h1 : (fun τ : ℍ => ModularGroup.S • τ) =
      (fun τ : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • τ) :=
    funext S_smul_eq_mapGL_smul
  rw [h1]
  exact UpperHalfPlane.mdifferentiable_smul mapGL_S_det_pos

end Work.Modular
