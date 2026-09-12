import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators
open scoped RealInnerProductSpace

theorem axis_isometry_coord0 {n : ℕ} [NeZero n]
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hfix : L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ))
    (v : EuclideanSpace ℝ (Fin n)) :
    (L v) (0 : Fin n) = v (0 : Fin n) := by
  let e0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  have hcoord : ∀ w : EuclideanSpace ℝ (Fin n), ⟪e0, w⟫ = w (0 : Fin n) := by
    intro w
    rw [EuclideanSpace.inner_single_left]
    simp
  have hmain : ⟪e0, L v⟫ = ⟪e0, v⟫ := by
    calc
      ⟪e0, L v⟫ = ⟪L e0, L v⟫ := by rw [hfix]
      _ = ⟪e0, v⟫ := by rw [L.inner_map_map]
  calc
    (L v) (0 : Fin n) = ⟪e0, L v⟫ := (hcoord (L v)).symm
    _ = ⟪e0, v⟫ := hmain
    _ = v (0 : Fin n) := hcoord v

end Commons.Analysis.InnerProductSpace