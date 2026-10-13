import Mathlib

namespace Work.WilE7

/-- Rank–nullity for a surjective linear map `ℝⁿ →ₗ[ℝ] ℝᵏ`: the kernel has dimension `n - k`. -/
theorem finrank_ker_of_surjective {n k : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (h : f.range = ⊤) : Module.finrank ℝ f.ker = n - k := by
  have hfr := LinearMap.finrank_range_add_finrank_ker f
  rw [h, finrank_top ℝ (Fin k → ℝ), Module.finrank_fin_fun ℝ, Module.finrank_fin_fun ℝ] at hfr
  omega

/-- The kernel of a surjective continuous linear map `ℝⁿ → ℝᵏ` is linearly homeomorphic to
`ℝ ^ (n - k)`: both are finite dimensional real vector spaces of the same dimension, and every
linear map between finite dimensional real spaces is continuous. -/
theorem exists_ker_equiv {n k : ℕ} (f : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ)) (h : f.range = ⊤) :
    Nonempty ((Fin (n - k) → ℝ) ≃L[ℝ] f.ker) := by
  have hdim : Module.finrank ℝ f.ker = n - k :=
    finrank_ker_of_surjective (f : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) h
  exact ⟨(LinearEquiv.ofFinrankEq _ _
    (by rw [Module.finrank_fin_fun, hdim])).toContinuousLinearEquiv⟩

end Work.WilE7
