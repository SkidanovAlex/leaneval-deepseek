import Mathlib

namespace Work.WilE7.DimAPI

theorem ker_comp_eq_ker_of_finrank_range_eq {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] V) (π : V →ₗ[ℝ] W)
    (h : Module.finrank ℝ (π.comp T).range = Module.finrank ℝ T.range) :
    (π.comp T).ker = T.ker := by
  -- `T.ker ≤ (π.comp T).ker` always holds; show the finranks are equal, then conclude.
  symm
  refine Submodule.eq_of_le_of_finrank_eq (LinearMap.ker_le_ker_comp T π) ?_
  -- rank–nullity for both `T` and `π.comp T`, then cancel the equal range finranks.
  have hT := LinearMap.finrank_range_add_finrank_ker T
  have hC := LinearMap.finrank_range_add_finrank_ker (π.comp T)
  have e : Module.finrank ℝ T.range + Module.finrank ℝ T.ker
      = Module.finrank ℝ (π.comp T).range + Module.finrank ℝ (π.comp T).ker := by
    rw [hT, hC]
  rw [h] at e
  exact Nat.add_left_cancel e

end Work.WilE7.DimAPI
