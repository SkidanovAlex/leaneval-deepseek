import Mathlib
import Submission.Work.Holonomy3.mv_lex_general_defs

/-!
# Measurability and a uniform bound for the polydisc holonomy function

Let `g` be a multivariable power series in `d` variables whose monomial series converges
(unconditionally, i.e. as a `HasSum` over the multi-index type `Fin d →₀ ℕ`) at every point of the
closed polydisc of radius `ρ > 1`, with sum `G z`. This file proves the two elementary facts about
the "holonomy function" `t ↦ ‖G (tor t)‖` on the parameter torus that are needed downstream:

* it is **measurable** (it is the pointwise limit of the continuous functions obtained by
  truncating the series to multi-indices of total degree `≤ N`);
* it is **uniformly bounded** by the sum of the norms of the coefficients:
  `‖G (tor t)‖ ≤ ∑' m, ‖coeff m g‖` for every `t`.

The summability of the coefficient norms is not assumed: it is derived from the hypothesis via
`Work.Holonomy3.mv_lex_coeff_summable` (unordered convergence on the polydisc of radius `ρ`
implies summability of the coefficient norms, because `ℂ` is finite dimensional).
-/

namespace Work.Holonomy3

open scoped BigOperators Topology
open Filter

noncomputable section

theorem mv_lex_measurable_norm_G {d : ℕ} (g : MvPowerSeries (Fin d) ℂ) (G : (Fin d → ℂ) → ℂ)
    {ρ : ℝ} (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z)) :
    Measurable (fun t : Fin d → ℝ => ‖G (tor t)‖) ∧
      (∀ t : Fin d → ℝ, ‖G (tor t)‖ ≤ ∑' m : Fin d →₀ ℕ, ‖MvPowerSeries.coeff m g‖) := by
  let c : (Fin d →₀ ℕ) → ℂ := fun m => MvPowerSeries.coeff m g
  have hr1 : 1 < (1 + ρ) / 2 := by linarith
  have hrρ : (1 + ρ) / 2 < ρ := by linarith
  -- Summability of the coefficients, from convergence on the polydisc of radius `ρ`.
  have hbig : Summable (fun m : Fin d →₀ ℕ => ‖c m‖ * ((1 + ρ) / 2) ^ m.degree) :=
    mv_lex_coeff_summable g G hρ hG hr1 hrρ
  have hsum : Summable (fun m : Fin d →₀ ℕ => ‖c m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hr1.le)) hbig
  have htor : ∀ t : Fin d → ℝ, ∀ j, ‖tor t j‖ ≤ ρ := fun t j => by
    rw [norm_tor_apply]; exact le_of_lt hρ
  constructor
  · -- Measurability: `t ↦ G (tor t)` is the pointwise limit of the degree truncations.
    have hcont : ∀ N : ℕ, Continuous fun t : Fin d → ℝ => pevalF (truncF c N) (tor t) := by
      intro N
      unfold pevalF tor
      fun_prop
    refine (measurable_of_tendsto_metrizable (f := fun N t => pevalF (truncF c N) (tor t))
      (fun N => (hcont N).measurable) ?_).norm
    rw [tendsto_pi_nhds]
    intro t
    have hHas := hG (tor t) (htor t)
    have hcomp : Tendsto (fun N : ℕ => ∑ m ∈ degLe d N, c m * ∏ j, tor t j ^ (m j))
        atTop (𝓝 (G (tor t))) := hHas.comp (tendsto_degLe d)
    convert hcomp using 2 with N
    exact pevalF_truncF_tor c N t
  · -- The uniform bound.
    intro t
    have hHas := hG (tor t) (htor t)
    have hnorm : HasSum (fun m : Fin d →₀ ℕ => ‖c m‖) (∑' m : Fin d →₀ ℕ, ‖c m‖) :=
      hsum.hasSum
    refine HasSum.norm_le_of_bounded hHas hnorm (fun m => ?_)
    rw [norm_mul]
    have hprod : (∏ j : Fin d, ‖tor t j ^ (m j)‖) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [norm_pow, norm_tor_apply, one_pow]
    rw [norm_prod, hprod, mul_one]

end

end Work.Holonomy3
