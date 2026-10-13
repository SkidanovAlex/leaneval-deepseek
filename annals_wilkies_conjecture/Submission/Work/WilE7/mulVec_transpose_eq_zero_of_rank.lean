import Mathlib

namespace Work.WilE7

theorem mulVec_transpose_eq_zero_of_rank {j q : ℕ} (M : Matrix (Fin j) (Fin q) ℝ) (hM : M.rank = j)
    (v : Fin j → ℝ) (hv : Matrix.mulVec (Matrix.transpose M) v = 0) : v = 0 := by
  -- `Mᵀ` has rank `j`, which is the dimension of its domain `Fin j → ℝ`, so `Mᵀ` is injective.
  have hrank : (Matrix.transpose M).rank = j := by rw [Matrix.rank_transpose, hM]
  have hker0 : Module.finrank ℝ (LinearMap.ker (Matrix.transpose M).mulVecLin) = 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.transpose M).mulVecLin
    rw [Matrix.rank] at hrank
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  have hkerbot : LinearMap.ker (Matrix.transpose M).mulVecLin = ⊥ :=
    (Submodule.finrank_eq_zero).mp hker0
  have hmem : v ∈ LinearMap.ker (Matrix.transpose M).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hv
  rw [hkerbot, Submodule.mem_bot] at hmem
  exact hmem

end Work.WilE7
