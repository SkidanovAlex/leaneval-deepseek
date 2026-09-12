import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.Analysis.InnerProductSpace.norm_map_exteriorPower_of_linearIsometry

namespace Commons.Analysis.InnerProductSpace

/-- **The exterior-power action of a linear isometry is isometric.**  For a linear isometry
equivalence `e` of a finite-dimensional real inner product space `E` and every `x : ⋀[ℝ]^n E`,
`‖exteriorPower.map n (e : E →ₗ[ℝ] E) x‖ = ‖x‖`.  Companion of the existing commons lemma
`Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry`. -/
theorem norm_exteriorPower_map_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (e : E ≃ₗᵢ[ℝ] E) (x : ⋀[ℝ]^n E) :
    ‖exteriorPower.map n (e : E →ₗ[ℝ] E) x‖ = ‖x‖ :=
  norm_map_exteriorPower_of_linearIsometry (k := n) e x

end Commons.Analysis.InnerProductSpace
