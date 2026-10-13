import Mathlib

namespace Work.WilE2

theorem exists_ne_zero_mem_ker_fderiv {m : ℕ} (hm : 2 ≤ m) (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (z : Fin m → ℝ) :
    ∃ v : Fin m → ℝ, v ≠ 0 ∧ fderiv ℝ V z v = 0 := by
  -- The derivative is a linear map from a space of dimension `m` to one of
  -- dimension `m - 1`; by rank-nullity its kernel is nontrivial.
  set f : (Fin m → ℝ) →ₗ[ℝ] (Fin (m - 1) → ℝ) := (fderiv ℝ V z).toLinearMap with hf
  have hker : f.ker ≠ ⊥ := by
    intro h
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp h
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv0, ?_⟩
  have h1 : f v = 0 := LinearMap.mem_ker.mp hv
  simpa [hf] using h1

end Work.WilE2
