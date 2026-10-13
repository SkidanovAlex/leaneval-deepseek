import Mathlib

namespace Work.WilE7.FrontierCS

/-- A surjective linear map `ℝ^N → ℝ^j` forces `j ≤ N`: the rank of a linear map is
bounded by the dimension of its domain, and surjectivity says the rank is `j`. -/
theorem le_of_range_top {N j : ℕ} (L : (Fin N → ℝ) →L[ℝ] (Fin j → ℝ)) (h : L.range = ⊤) :
    j ≤ N := by
  have hle : Module.finrank ℝ L.range ≤ N := by
    have := LinearMap.finrank_range_le (L : (Fin N → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  have heq : Module.finrank ℝ L.range = j := by
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

end Work.WilE7.FrontierCS
