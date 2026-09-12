import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

theorem axis_isometry_preserves_compl_norm {n : ℕ} [NeZero n]
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hfix : L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ))
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖L v - (v (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ =
      ‖v - (v (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  have hmap : L (v - (v (0 : Fin n)) • e) = L v - (v (0 : Fin n)) • e := by
    rw [map_sub, map_smul, hfix]
  rw [← hmap]
  exact L.norm_map (v - (v (0 : Fin n)) • e)

end Commons.Analysis.InnerProductSpace