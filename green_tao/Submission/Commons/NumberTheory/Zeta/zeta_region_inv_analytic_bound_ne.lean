import Mathlib
import Submission.Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_log_zeroFree

namespace Commons.NumberTheory.Zeta

/-- **The reciprocal of `ζ` is holomorphic and `≪ log(|Im z|+2)` in a log-width
zero-free region just to the right of the critical line.**

There is a width `β₀ ∈ (0, 1/10]` and a constant `C > 0` such that for every
nonzero `z : ℂ` with `-(β₀ / log(|z.im|+2)) ≤ z.re ≤ 1`:
* `ζ(1+z) ≠ 0`,
* `u ↦ (ζ(1+u))⁻¹` is complex differentiable at `z`, and
* `‖(ζ(1+z))⁻¹‖ ≤ C (log(|z.im|+2) + 1)`.

This is obtained by combining the all-height zero-free region
(`zeta_ne_zero_log_zeroFree`) with the bound `1/ζ ≪ log` in the same region
(`inv_zeta_le_log_zeroFree`); both are stated for the argument `σ + i t` with
`1 - c/log(|t|+2) ≤ σ ≤ 2`, which is exactly the image of the region here under
`z ↦ 1 + z`. -/
theorem zeta_region_inv_analytic_bound_ne :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 10 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, z ≠ 0 → -(β₀ / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        riemannZeta (1 + z) ≠ 0 ∧
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C * (Real.log (|z.im| + 2) + 1) := by
  -- Zero-free region at all heights, and the `1/ζ ≪ log` bound in the same region.
  obtain ⟨c₁, hc₁, hzf⟩ := zeta_ne_zero_log_zeroFree
  obtain ⟨c₂, C, hc₂, hC, hbd⟩ := inv_zeta_le_log_zeroFree
  refine ⟨min (min c₁ c₂) (1 / 10),
    lt_min (lt_min hc₁ hc₂) (by norm_num), min_le_right _ _, C, hC, ?_⟩
  intro z hz hlower hupper
  -- The argument `1 + z` written in the `σ + i t` shape used by the commons lemmas.
  have hs_eq : ((1 + z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = 1 + z := by
    apply Complex.ext <;> simp
  have hlogpos : 0 < Real.log (|z.im| + 2) :=
    Real.log_pos (by linarith [abs_nonneg z.im])
  have hβ₁ : min (min c₁ c₂) (1 / 10) ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hβ₂ : min (min c₁ c₂) (1 / 10) ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hσlo₁ : 1 - c₁ / Real.log (|z.im| + 2) ≤ 1 + z.re := by
    have hβ : min (min c₁ c₂) (1 / 10) / Real.log (|z.im| + 2) ≤ c₁ / Real.log (|z.im| + 2) :=
      div_le_div_of_nonneg_right hβ₁ (le_of_lt hlogpos)
    linarith
  have hσlo₂ : 1 - c₂ / Real.log (|z.im| + 2) ≤ 1 + z.re := by
    have hβ : min (min c₁ c₂) (1 / 10) / Real.log (|z.im| + 2) ≤ c₂ / Real.log (|z.im| + 2) :=
      div_le_div_of_nonneg_right hβ₂ (le_of_lt hlogpos)
    linarith
  have hσhi : 1 + z.re ≤ 2 := by linarith
  -- Non-vanishing.
  have hne : riemannZeta (1 + z) ≠ 0 := by
    have h := hzf (1 + z.re) z.im hσlo₁ hσhi
    rwa [hs_eq] at h
  -- Differentiability of the reciprocal.
  have hne1 : 1 + z ≠ 1 := fun hc => hz (by linear_combination hc)
  have hdiff : DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z :=
    ((differentiableAt_riemannZeta hne1).comp z (by fun_prop)).inv hne
  -- The quantitative bound.
  have hnorm : ‖(riemannZeta (1 + z))⁻¹‖ ≤ C * (Real.log (|z.im| + 2) + 1) := by
    have hb := hbd (1 + z.re) z.im hσlo₂ hσhi
    rw [hs_eq, one_div, ← norm_inv] at hb
    exact hb
  exact ⟨hne, hdiff, hnorm⟩

end Commons.NumberTheory.Zeta
