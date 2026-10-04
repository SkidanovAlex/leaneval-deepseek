import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.MatGlob

/-- Entrywise (`ℓ¹`-type) bound for a linear functional on `Fin n → ℝ`: evaluating `L` at a vector
`w` costs at most the sum of the absolute values of the images of the standard basis vectors,
multiplied by the sup norm of `w`. This is the "`|L w| ≤ (∑ₛ |L (eₛ)|) · ‖w‖" estimate that bounds
a linear functional by its values on the standard basis. -/
theorem abs_clm_apply_le {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (w : Fin n → ℝ) :
    |L w| ≤ (∑ s : Fin n, |L (Pi.single s (1 : ℝ))|) * ‖w‖ := by
  have hw : w = ∑ s : Fin n, w s • (Pi.single s (1 : ℝ) : Fin n → ℝ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  have hLw : L w = ∑ s : Fin n, w s * L (Pi.single s (1 : ℝ)) := by
    conv_lhs => rw [hw]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun s _ => by rw [map_smul, smul_eq_mul])
  calc |L w| = |∑ s : Fin n, w s * L (Pi.single s (1 : ℝ))| := by rw [hLw]
    _ ≤ ∑ s : Fin n, |w s * L (Pi.single s (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin n, ‖w‖ * |L (Pi.single s (1 : ℝ))| := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm w s) (abs_nonneg _)
    _ = (∑ s : Fin n, |L (Pi.single s (1 : ℝ))|) * ‖w‖ := by
        rw [← Finset.mul_sum, mul_comm]

end Work.Diff.STE.B3.MatGlob
