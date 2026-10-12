import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.flatConsistencyArith`

The scalar consistency inequality of FS §5 (the flat-family constraint, see
`Submission/Work/BoseFixB1/perSectorBoundG_FINDING.md` §1b): with the `1`-weight
`F(t) = psiWeight 1 μ t` (`F(t) = (t-μ)²/(1 + tμ⁻¹)`),

  `c ≤ γ/4` and `c ≤ 1/8` imply `c(F(ρ) + μ²) ≤ (ρ-μ)²/2 + γρ²/2` for every `ρ ≥ 0`.

The proof is a two-step reduction:
* `F(ρ) ≤ (ρ-μ)²`, since the denominator `1 + ρμ⁻¹ ≥ 1` (here `ρ ≥ 0`, `μ > 0`);
* the polynomial inequality `c((ρ-μ)²+μ²) ≤ (ρ-μ)²/2 + γρ²/2`, i.e.
  `0 ≤ a(ρ-μ)² + bρ² - cμ²` with `a = 1/2 - c`, `b = γ/2`, which follows from the
  exact algebraic identity
  `(a+b)(a(ρ-μ)² + bρ² - cμ²) = (a(μ-ρ) - bρ)² + (ab - c(a+b))μ²`
  together with `ab - c(a+b) ≥ 0` (a consequence of `c ≤ 1/8` and `c ≤ γ/4`).

For `c ≤ 0` the inequality is trivial (both sides have the sign forced by the
hypotheses).
-/

namespace Work.BoseFixB1

theorem flatConsistencyArith (μ γ c : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hc1 : c ≤ γ / 4) (hc2 : c ≤ 1 / 8) :
    ∀ ρ : ℝ, 0 ≤ ρ →
      c * (Work.SmallBoxSliding.psiWeight 1 μ ρ + μ ^ 2)
        ≤ (ρ - μ) ^ 2 / 2 + γ * ρ ^ 2 / 2 := by
  intro ρ hρ
  have hμinv : 0 ≤ μ⁻¹ := le_of_lt (inv_pos.mpr hμ)
  have hden : 0 < 1 + ρ * μ⁻¹ := by
    have : 0 ≤ ρ * μ⁻¹ := mul_nonneg hρ hμinv
    linarith
  -- `F(ρ) ≤ (ρ-μ)²`: the denominator is at least one.
  have hpsi : Work.SmallBoxSliding.psiWeight 1 μ ρ ≤ (ρ - μ) ^ 2 := by
    rw [Work.SmallBoxSliding.psiWeight, one_mul, div_le_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (ρ - μ)) hμinv) hρ]
  have hpsi_nn : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ ρ := by
    rw [Work.SmallBoxSliding.psiWeight, one_mul]
    exact div_nonneg (sq_nonneg _) (le_of_lt hden)
  by_cases hc : c ≤ 0
  · -- `c ≤ 0`: the left side is `≤ 0`, the right side is `≥ 0`.
    have h1 : c * (Work.SmallBoxSliding.psiWeight 1 μ ρ + μ ^ 2) ≤ 0 := by
      have h0 : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ ρ + μ ^ 2 := by
        have := sq_nonneg μ; linarith
      nlinarith
    have h2 : 0 ≤ (ρ - μ) ^ 2 / 2 + γ * ρ ^ 2 / 2 := by
      have h1 := sq_nonneg (ρ - μ); have h2 := sq_nonneg ρ; nlinarith
    linarith
  · have hcpos : 0 < c := lt_of_not_ge hc
    -- the key polynomial inequality: `a(ρ-μ)² + bρ² - cμ² ≥ 0`, `a = 1/2-c`, `b = γ/2`.
    have hN : 0 ≤ (1 / 2 - c) * (γ / 2) - c * ((1 / 2 - c) + γ / 2) := by
      nlinarith [hcpos, hc1, hc2, hγ]
    have hident :
        ((1 / 2 - c) + γ / 2) * ((1 / 2 - c) * (μ - ρ) ^ 2 + (γ / 2) * ρ ^ 2 - c * μ ^ 2)
          = ((1 / 2 - c) * (μ - ρ) - (γ / 2) * ρ) ^ 2
            + ((1 / 2 - c) * (γ / 2) - c * ((1 / 2 - c) + γ / 2)) * μ ^ 2 := by ring
    have hP : 0 ≤ (1 / 2 - c) * (μ - ρ) ^ 2 + (γ / 2) * ρ ^ 2 - c * μ ^ 2 := by
      have hs : 0 ≤ ((1 / 2 - c) * (μ - ρ) - (γ / 2) * ρ) ^ 2 := sq_nonneg _
      have hNmu : 0 ≤ ((1 / 2 - c) * (γ / 2) - c * ((1 / 2 - c) + γ / 2)) * μ ^ 2 :=
        mul_nonneg hN (sq_nonneg μ)
      have hsum :
          0 ≤ ((1 / 2 - c) + γ / 2) * ((1 / 2 - c) * (μ - ρ) ^ 2 + (γ / 2) * ρ ^ 2 - c * μ ^ 2) := by
        rw [hident]; linarith
      have hpos : 0 < (1 / 2 - c) + γ / 2 := by linarith
      exact nonneg_of_mul_nonneg_right hsum hpos
    have hkey : c * ((ρ - μ) ^ 2 + μ ^ 2) ≤ (ρ - μ) ^ 2 / 2 + γ * ρ ^ 2 / 2 := by
      nlinarith [hP]
    have hle : c * (Work.SmallBoxSliding.psiWeight 1 μ ρ + μ ^ 2)
        ≤ c * ((ρ - μ) ^ 2 + μ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hpsi (le_of_lt hcpos)
      linarith
    linarith

end Work.BoseFixB1
