import Mathlib

/-!
# The chart model map of the compact `n = 2` construction

`incl23 : ℝ² →L[ℝ] ℝ³` is the inclusion into the first two coordinates (used to draw the chart model
of a critical point inside `ℝ³`), and `chartModel φ shift : M → ℝ³` is the model map
`y ↦ incl23 (φ y) + shift` of a Morse chart `φ`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- The inclusion `ℝ² → ℝ³` into the first two coordinates, as a continuous linear map. -/
noncomputable def incl23 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 =>
      if i = 0 then (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0)
      else if i = 1 then (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1)
      else 0))

/-- The chart model map: `y ↦ incl23 (φ y) + shift`. -/
noncomputable def chartModel {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (shift : EuclideanSpace ℝ (Fin 3)) : M → EuclideanSpace ℝ (Fin 3) :=
  fun y => incl23 (φ y) + shift

end Work.Drive.N2
