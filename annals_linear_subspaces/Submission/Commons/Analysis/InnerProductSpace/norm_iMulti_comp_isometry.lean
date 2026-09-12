import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.Analysis.InnerProductSpace.norm_map_exteriorPower_of_linearIsometry

namespace Commons.Analysis.InnerProductSpace

open exteriorPower

theorem norm_iMulti_comp_isometry {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e : E ≃ₗᵢ[ℝ] E) {n : ℕ}
    (b : Fin n → E) :
    ‖exteriorPower.ιMulti ℝ n (fun i => e (b i))‖ = ‖exteriorPower.ιMulti ℝ n b‖ := by
  have hco : (e : E →ₗ[ℝ] E) ∘ b = fun i => e (b i) := by
    funext i
    simp
  have hmap' : exteriorPower.map n (e : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ n b) =
      exteriorPower.ιMulti ℝ n ((e : E →ₗ[ℝ] E) ∘ b) := by
    simp
  have hmap : exteriorPower.ιMulti ℝ n (fun i => e (b i)) =
      exteriorPower.map n (e : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ n b) := by
    rw [← hco]
    rw [← hmap']
  calc
    ‖exteriorPower.ιMulti ℝ n (fun i => e (b i))‖
        = ‖exteriorPower.map n (e : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ n b)‖ := by rw [hmap]
    _ = ‖exteriorPower.ιMulti ℝ n b‖ := by
      exact norm_map_exteriorPower_of_linearIsometry (k := n) e (exteriorPower.ιMulti ℝ n b)

end Commons.Analysis.InnerProductSpace
