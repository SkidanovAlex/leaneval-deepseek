import Mathlib
import Submission.Commons.NumberTheory.Zeta.sigma_mul_zeta_one_add_tendsto_one

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped Topology

/-- Near `s = 1`, on the real axis, the Riemann zeta function dominates `1/(2(σ-1))`.

This is the quantitative form of the fact that `ζ` has a simple pole of residue `1` at
`s = 1`: along the real axis `ζ(1+h) ~ 1/h` as `h → 0⁺`.  We obtain it from the residue
asymptotic `σ · ζ(1+σ) → 1` (`σ → 0⁺`): for `σ > 0` small enough we have
`σ · Re ζ(1+σ) > 1/2`, whence `Re ζ(1+σ) > 1/(2σ)` and `|ζ(1+σ)| ≥ Re ζ(1+σ)`. -/
theorem riemannZeta_lower_bound_near_one :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      1 / (2 * (σ - 1)) ≤ ‖riemannZeta (σ : ℂ)‖ := by
  -- The residue asymptotic: `σ * Re ζ(1+σ) → 1` as `σ → 0⁺`.
  have htend := Commons.NumberTheory.Zeta.sigma_mul_zeta_one_add_tendsto_one
  have hev : ∀ᶠ σ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (1 / 2 : ℝ) < σ * (riemannZeta ((1 : ℂ) + (σ : ℂ))).re :=
    (tendsto_order.1 htend).1 (1 / 2) (by norm_num)
  -- Turn the `∀ᶠ` statement into an explicit `ε`.
  rw [eventually_nhdsWithin_iff] at hev
  rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hε, hε'⟩
  refine ⟨ε, hε, ?_⟩
  intro σ hσ1 hσε
  have hhpos : 0 < σ - 1 := by linarith
  have hhlt : σ - 1 < ε := by linarith
  have hdist : dist (σ - 1) 0 < ε := by
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hhpos]
    exact hhlt
  have hP : (1 / 2 : ℝ) < (σ - 1) * (riemannZeta ((1 : ℂ) + ((σ - 1 : ℝ) : ℂ))).re :=
    hε' (y := σ - 1) hdist hhpos
  have h2 : (1 : ℝ) / (2 * (σ - 1)) <
      (riemannZeta ((1 : ℂ) + ((σ - 1 : ℝ) : ℂ))).re := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (σ - 1))]
    nlinarith [hP]
  have h4 : (riemannZeta ((1 : ℂ) + ((σ - 1 : ℝ) : ℂ))).re ≤
      ‖riemannZeta ((1 : ℂ) + ((σ - 1 : ℝ) : ℂ))‖ := Complex.re_le_norm _
  have hσeq : (σ : ℂ) = (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]; ring
  rw [hσeq]
  exact le_trans (le_of_lt h2) h4

end Work.FIArea6Hecke.R
