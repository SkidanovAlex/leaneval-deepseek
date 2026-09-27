import Mathlib

namespace Work.Whitney

open Polynomial

/-- If `R` is a square-zero continuous endomorphism of a finite-dimensional real normed space,
then `1 + R` is unipotent and has determinant `1`. -/
theorem det_one_add_of_sq_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E →L[ℝ] E) (hR : R * R = 0) :
    LinearMap.det ((1 + R : E →L[ℝ] E)).toLinearMap = 1 := by
  -- `R` is nilpotent as an endomorphism, hence so is `-R`, whose characteristic polynomial
  -- is therefore `X ^ finrank ℝ E`; evaluating `eval_charpoly` at `1` gives the result.
  have hnil : IsNilpotent (R : E →L[ℝ] E) := ⟨2, by rw [pow_two]; exact hR⟩
  have hnil' : IsNilpotent (-(R.toLinearMap : Module.End ℝ E)) :=
    (hnil.map ContinuousLinearMap.toLinearMapRingHom).neg
  have hcp : (-(R.toLinearMap : Module.End ℝ E)).charpoly = (X : ℝ[X]) ^ Module.finrank ℝ E :=
    IsNilpotent.charpoly_eq_X_pow_finrank hnil'
  have h1 : ((1 : Module.End ℝ E) + R.toLinearMap).det =
      (-(R.toLinearMap : Module.End ℝ E)).charpoly.eval 1 := by
    rw [LinearMap.eval_charpoly]
    simp
  have h2 : ((1 + R : E →L[ℝ] E)).toLinearMap = (1 : Module.End ℝ E) + R.toLinearMap := by
    simp
  rw [h2, h1, hcp]
  simp

end Work.Whitney
