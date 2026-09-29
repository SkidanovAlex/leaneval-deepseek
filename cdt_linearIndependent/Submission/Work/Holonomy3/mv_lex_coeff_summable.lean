import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

/-!
# Coefficient summability on a smaller polydisc

If the multivariable power series `g` evaluated at every point of the closed polydisc of radius `ρ`
has an (unordered) sum, then the coefficients of `g` grow at most geometrically with ratio `1/ρ`:
for every `r < ρ` the family `m ↦ ‖coeff m g‖ * r ^ m.degree` is summable.

The point is that `HasSum` over the index type `Fin d →₀ ℕ` is *unordered* summation. Since `ℂ` is
finite dimensional, unordered convergence implies absolute convergence on the polydisc of radius
`ρ` (`summable_norm_iff`/`Summable.norm`), and `ℂ` coefficients can be bounded by the geometric
series of ratio `r / ρ < 1`.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- The monomial `∏ j, a ^ (m j)` only depends on the total degree of `m`. -/
theorem prod_pow_degree {d : ℕ} (a : ℂ) (m : Fin d →₀ ℕ) :
    ∏ j, a ^ (m j) = a ^ m.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.prod_pow_eq_pow_sum Finset.univ m a

theorem mv_lex_coeff_summable {d : ℕ} (g : MvPowerSeries (Fin d) ℂ) (G : (Fin d → ℂ) → ℂ) {ρ : ℝ} (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z))
    {r : ℝ} (hr1 : 1 < r) (hrρ : r < ρ) :
    Summable (fun m : Fin d →₀ ℕ => ‖MvPowerSeries.coeff m g‖ * r ^ m.degree) := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  -- Summability of the series at the boundary point `(ρ, …, ρ)` of the polydisc.
  have hsumρ : Summable (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * (ρ : ℂ) ^ m.degree) := by
    have hz : ∀ j : Fin d, ‖((ρ : ℝ) : ℂ)‖ ≤ ρ := fun _ =>
      le_of_eq (Complex.norm_of_nonneg hρpos.le)
    have h := (hG (fun _ : Fin d => ((ρ : ℝ) : ℂ)) hz).summable
    refine h.congr (fun m => ?_)
    rw [prod_pow_degree]
  -- Hence the series is absolutely summable on that polydisc.
  have hnormρ : Summable (fun m : Fin d →₀ ℕ => ‖MvPowerSeries.coeff m g‖ * ρ ^ m.degree) := by
    have h := hsumρ.norm
    refine h.congr (fun m => ?_)
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hρpos.le]
  -- Dominate the coefficients at radius `r` by those at radius `ρ`.
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hnormρ
  · positivity
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hrpos.le hrρ.le m.degree) (norm_nonneg _)

end Work.Holonomy3
