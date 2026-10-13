import Mathlib

namespace Work.WilCrux

theorem clm_norm_le_sum_eval (b : ℕ) (L : (Fin b → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ j : Fin b, ‖L (Pi.single j (1 : ℝ))‖ := by
  classical
  refine L.opNorm_le_bound (by positivity) (fun x => ?_)
  have hx : L x = ∑ j : Fin b, x j * L (Pi.single j (1 : ℝ)) := by
    have hdecomp : (∑ j : Fin b, x j • Pi.single j (1 : ℝ)) = x := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    calc L x = L (∑ j : Fin b, x j • Pi.single j (1 : ℝ)) := by rw [hdecomp]
      _ = ∑ j : Fin b, L (x j • Pi.single j (1 : ℝ)) := by rw [map_sum]
      _ = ∑ j : Fin b, x j * L (Pi.single j (1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [map_smul, smul_eq_mul]
  rw [hx]
  calc ‖∑ j : Fin b, x j * L (Pi.single j (1 : ℝ))‖
      ≤ ∑ j : Fin b, ‖x j * L (Pi.single j (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ j : Fin b, ‖x j‖ * ‖L (Pi.single j (1 : ℝ))‖ := by simp [norm_mul]
    _ ≤ ∑ j : Fin b, ‖x‖ * ‖L (Pi.single j (1 : ℝ))‖ := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j : Fin b, ‖L (Pi.single j (1 : ℝ))‖) * ‖x‖ := by
          rw [mul_comm, Finset.mul_sum]

end Work.WilCrux
