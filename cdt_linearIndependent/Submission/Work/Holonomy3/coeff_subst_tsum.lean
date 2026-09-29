import Mathlib

namespace Work.Holonomy3

/-- Coefficient of a substituted power series as a (finite) sum over the coefficients
of the outer series: if `ψ` has zero constant term, then for every `k`,
`[X^k] h(ψ) = ∑_d [X^d] h · [X^k] ψ^d`.  The sum is finite because `ψ^d` has order
at least `d`. -/
theorem coeff_subst_tsum {h ψ : PowerSeries ℂ} (hψ0 : PowerSeries.coeff 0 ψ = 0) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.subst ψ h)
      = ∑' d : ℕ, PowerSeries.coeff d h * PowerSeries.coeff k (ψ ^ d) := by
  have hψ : PowerSeries.HasSubst ψ :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      have := hψ0
      rwa [PowerSeries.coeff_zero_eq_constantCoeff] at this)
  rw [PowerSeries.coeff_subst' hψ h k,
    ← tsum_eq_finsum (L := SummationFilter.unconditional ℕ)
      (PowerSeries.coeff_subst_finite' hψ h k)]
  exact tsum_congr fun d => by simp

end Work.Holonomy3
