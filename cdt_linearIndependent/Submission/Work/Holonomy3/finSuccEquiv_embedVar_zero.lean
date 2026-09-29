import Mathlib
import Submission.Work.Holonomy3.aux_defs

namespace Work.Holonomy3

open MvPowerSeries PowerSeries

/-- The coefficients of `embedVar s g` are the coefficients of `g`, read at the exponent of the
variable `X s`, together with the constraint that all other exponents vanish. -/
private lemma coeff_embedVar {d : ℕ} (s : Fin d) (g : PowerSeries ℚ) (m : Fin d →₀ ℕ) :
    MvPowerSeries.coeff m (Submission.CDTPlan.embedVar s g)
      = if m = Finsupp.single s (m s) then PowerSeries.coeff (m s) g else 0 := rfl

/-- The image under `MvPowerSeries.finSuccEquiv` (`X 0 ↦ X`, `X (j+1) ↦ C (X j)`) of the series
`embedVar 0 g = Σ_k (coeff k g)·X_0^k` (a series in the single variable `X 0`) is the series
`PowerSeries.map (algebraMap ℚ ℚ⟦X_1..X_n⟧) g = Σ_k (coeff k g)·X^k`, i.e. the same series in the
outer variable.  Proof: `PowerSeries.ext` in `k`, `MvPowerSeries.ext` in `x`, then
`MvPowerSeries.coeff_coeff_finSuccEquiv` (giving `coeff (x.cons k) (embedVar 0 g)`) and
`Finsupp.cons_eq_single_zero_iff`. -/
lemma finSuccEquiv_embedVar_zero {n : ℕ} (g : PowerSeries ℚ) :
    MvPowerSeries.finSuccEquiv ℚ n (Submission.CDTPlan.embedVar (0 : Fin (n + 1)) g)
      = PowerSeries.map (algebraMap ℚ (MvPowerSeries (Fin n) ℚ)) g := by
  ext k x
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, coeff_embedVar, PowerSeries.coeff_map,
    MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  simp only [Finsupp.cons_zero, Finsupp.cons_eq_single_zero_iff]
  by_cases hx : x = 0 <;> simp [hx]

end Work.Holonomy3
