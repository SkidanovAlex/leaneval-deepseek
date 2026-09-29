import Mathlib
import Submission.Work.Holonomy3.cleared_defs
import Submission.Work.Holonomy3.coeff_subst_tsum

/-!
# The `compPS` / `PowerSeries.subst` bridge

`Work.Holonomy3.compPS Φ F` is the formal composition of univariate power series over `ℂ`
defined by its coefficient formula `(compPS Φ F).coeff m = ∑_{k ≤ m} F_k · (Φ^k).coeff m`
(see `Submission/Work/Holonomy3/cleared_defs.lean`).  Mathlib's `PowerSeries.subst Φ F`
is the composition `F ∘ Φ` given by the substitution `X ↦ Φ`.

When `Φ` has vanishing constant coefficient the two agree: for `d > m` the coefficient
`[X^m] Φ^d` vanishes (`coeff_pow_eq_zero_of_lt`), so the Cauchy formula
`[X^m] h(ψ) = ∑_d [X^d] h · [X^m] ψ^d` of `coeff_subst_tsum` reduces to the finite sum
over `k ∈ range (m+1)` that defines `compPS`.
-/

namespace Work.Holonomy3

/-- `compPS ψ h = PowerSeries.subst ψ h` whenever `ψ` has vanishing constant coefficient:
the two coefficient formulas differ only by the terms `k > n`, which vanish by
`coeff_pow_eq_zero_of_lt`. -/
theorem compPS_subst_bridge {ψ h : PowerSeries ℂ} (hψ : PowerSeries.coeff 0 ψ = 0) :
    Work.Holonomy3.compPS ψ h = PowerSeries.subst ψ h := by
  ext n
  rw [compPS_coeff, coeff_subst_tsum hψ]
  refine (tsum_eq_sum (s := Finset.range (n + 1)) ?_).symm
  intro d hd
  have hdn : n < d := by
    simp only [Finset.mem_range] at hd
    omega
  rw [coeff_pow_eq_zero_of_lt hψ hdn, mul_zero]

end Work.Holonomy3
