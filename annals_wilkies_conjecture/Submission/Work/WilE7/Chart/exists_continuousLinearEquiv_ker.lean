import Mathlib

namespace Work.WilE7.Chart

open Module

theorem exists_continuousLinearEquiv_ker {q j : ℕ} (f : (Fin q → ℝ) →L[ℝ] (Fin j → ℝ))
    (h : f.range = ⊤) : Nonempty ((Fin (q - j) → ℝ) ≃L[ℝ] f.ker) := by
  -- The kernel of a surjective map `ℝ^q → ℝ^j` has dimension `q - j`, so it is
  -- (continuously, linearly) equivalent to `ℝ^(q-j)`.
  have hker : Module.finrank ℝ f.ker = q - j := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (f : (Fin q → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    have hfr : Module.finrank ℝ f.range = j := by
      rw [h, finrank_top]
      exact Module.finrank_fin_fun ℝ
    have hdom : Module.finrank ℝ (Fin q → ℝ) = q := Module.finrank_fin_fun ℝ
    rw [hfr, hdom] at hrn
    omega
  refine FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq ?_
  rw [Module.finrank_fin_fun, hker]

end Work.WilE7.Chart
