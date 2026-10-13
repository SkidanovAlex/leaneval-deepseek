import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

/-- Elementary weighted decay bound: for `ρ ≥ 0`, `p, lam, b > 0` with `p * lam ≥ 2`,

`ρ * (1 + ρ^p / b)^(-lam) ≤ 2 * max 1 (b^lam) / (1 + ρ)`.

The two regimes are `ρ ≤ 1` (where the rpow factor is at most `1`) and `ρ ≥ 1`
(where `(1 + ρ^p/b)^(-lam) ≤ (ρ^p/b)^(-lam) = ρ^(-p*lam) * b^lam`, and
`ρ^(1 - p*lam) ≤ ρ^(-1)` because `p * lam ≥ 2`). -/
theorem rho_mul_rpow_weight_le_two {p lam b ρ : ℝ} (hp : 0 < p) (hlam : 0 < lam) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hpl : 2 ≤ p * lam) :
    ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
  have hM1 : (1 : ℝ) ≤ max 1 (b ^ lam) := le_max_left _ _
  have hMb : b ^ lam ≤ max 1 (b ^ lam) := le_max_right _ _
  have hMpos : (0 : ℝ) < max 1 (b ^ lam) := lt_of_lt_of_le one_pos hM1
  rcases lt_or_ge ρ 1 with hρ1 | hρ1
  · -- small `ρ`: the rpow factor is at most `1`
    have hbase : (1 : ℝ) ≤ 1 + ρ ^ p / b := by
      have : 0 ≤ ρ ^ p / b := div_nonneg (Real.rpow_nonneg hρ p) hb.le
      linarith
    have hpw : (1 + ρ ^ p / b) ^ (-lam) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos one_pos hbase (show -lam ≤ 0 by linarith)
      rwa [Real.one_rpow] at h
    have h1 : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ ρ := by
      simpa using mul_le_mul_of_nonneg_left hpw hρ
    have h2 : ρ ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ρ)]
      nlinarith [hρ, hρ1, hM1]
    linarith
  · -- large `ρ`: `(1 + ρ^p/b)^(-lam) ≤ (ρ^p/b)^(-lam) = ρ^(-p*lam) * b^lam`
    have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hρ1
    have hspos : 0 < ρ ^ p / b := div_pos (Real.rpow_pos_of_pos hρpos p) hb
    have hbase2 : ρ ^ p / b ≤ 1 + ρ ^ p / b := by linarith
    have hpw : (1 + ρ ^ p / b) ^ (-lam) ≤ (ρ ^ p / b) ^ (-lam) :=
      Real.rpow_le_rpow_of_nonpos hspos hbase2 (show -lam ≤ 0 by linarith)
    have hA : (ρ ^ p / b) ^ (-lam) = ρ ^ (p * (-lam)) * b ^ lam := by
      rw [Real.div_rpow (Real.rpow_nonneg hρ p) hb.le, Real.rpow_neg hb.le,
          ← Real.rpow_mul hρ p (-lam)]
      rw [div_inv_eq_mul]
    have hcomb : ρ * ρ ^ (p * (-lam)) = ρ ^ (1 + p * (-lam)) := by
      rw [Real.rpow_add hρpos 1 (p * (-lam)), Real.rpow_one]
    have hexp : ρ ^ (1 + p * (-lam)) ≤ ρ ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hρ1 (by nlinarith [hpl])
    have hblam : 0 ≤ b ^ lam := (Real.rpow_pos_of_pos hb lam).le
    have hrhoinv : ρ ^ (-1 : ℝ) = ρ⁻¹ := by
      rw [Real.rpow_neg hρ 1, Real.rpow_one]
    have hfin : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ max 1 (b ^ lam) / ρ := by
      calc ρ * (1 + ρ ^ p / b) ^ (-lam)
          ≤ ρ * (ρ ^ p / b) ^ (-lam) := mul_le_mul_of_nonneg_left hpw hρ
        _ = ρ * ρ ^ (p * (-lam)) * b ^ lam := by rw [hA]; ring
        _ = ρ ^ (1 + p * (-lam)) * b ^ lam := by rw [hcomb]
        _ ≤ ρ ^ (-1 : ℝ) * max 1 (b ^ lam) :=
              mul_le_mul hexp hMb hblam (Real.rpow_nonneg hρ (-1))
        _ = max 1 (b ^ lam) / ρ := by rw [hrhoinv, div_eq_mul_inv]; ring
    have hlast : max 1 (b ^ lam) / ρ ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ρ)]
      rw [div_mul_eq_mul_div, div_le_iff₀ hρpos]
      nlinarith [hρ1, hMpos]
    linarith

end Work.FTS.BSIdent.Weyl.Levels
