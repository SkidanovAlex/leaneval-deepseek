import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Norm

theorem norm_le_sum_abs_coord {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖ξ‖ ≤ ∑ i : Fin d, |ξ i| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  have h2 : ∑ i : Fin d, |ξ i| ^ 2 ≤ (∑ i : Fin d, |ξ i|) ^ 2 := by
    simpa using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin d => |ξ i|) (fun i _ => abs_nonneg (ξ i)))
  calc √(∑ i : Fin d, |ξ i| ^ 2)
      ≤ √((∑ i : Fin d, |ξ i|) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ∑ i : Fin d, |ξ i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

end Commons.Analysis.Norm