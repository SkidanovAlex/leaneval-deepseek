import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

theorem bsDerivCLM_bound_arith {α δ S M H Q P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hδ : 0 ≤ δ) (hδS : δ ≤ S)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (hQP : Q ≤ P) (hP : 0 ≤ P) :
    4 * (2 * (M * δ)) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * Q ^ (α * (1 - α)) / (α * (1 - α)))
      + (4 * Real.pi / 3) * (M * δ)
    ≤ (4 * (2 * M) ^ α * (2 * H) ^ (1 - α) *
          (4 * Real.pi * P ^ (α * (1 - α)) / (α * (1 - α)))
        + (4 * Real.pi / 3) * (M * max 1 S)) * δ ^ α := by
  have hs : 0 < α * (1 - α) := by nlinarith
  have hQp : Q ^ (α * (1 - α)) ≤ P ^ (α * (1 - α)) :=
    Real.rpow_le_rpow hQ hQP (le_of_lt hs)
  -- First term: `4*(2(Mδ))^α (2H)^(1-α) (4π Q^s/s) ≤ 4*(2M)^α (2H)^(1-α) (4π P^s/s) δ^α`
  have hA : 4 * (2 * (M * δ)) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * Q ^ (α * (1 - α)) / (α * (1 - α)))
      ≤ 4 * (2 * M) ^ α * (2 * H) ^ (1 - α) *
          (4 * Real.pi * P ^ (α * (1 - α)) / (α * (1 - α))) * δ ^ α := by
    have hrw : (2 * (M * δ)) ^ α = (2 * M) ^ α * δ ^ α := by
      rw [show 2 * (M * δ) = 2 * M * δ by ring]
      exact Real.mul_rpow (by linarith : (0:ℝ) ≤ 2 * M) hδ
    rw [hrw]
    have hC : 0 ≤ 4 * (2 * M) ^ α * (2 * H) ^ (1 - α) * (4 * Real.pi / (α * (1 - α))) * δ ^ α := by
      have ha : (0:ℝ) ≤ (2 * M) ^ α := Real.rpow_nonneg (by linarith) _
      have hb : (0:ℝ) ≤ (2 * H) ^ (1 - α) := Real.rpow_nonneg (by linarith) _
      have hc : (0:ℝ) ≤ δ ^ α := Real.rpow_nonneg hδ _
      have hd : (0:ℝ) ≤ 4 * Real.pi / (α * (1 - α)) :=
        div_nonneg (by positivity) (le_of_lt hs)
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hb) hd) hc
    calc 4 * ((2 * M) ^ α * δ ^ α) * (2 * H) ^ (1 - α) *
            (4 * Real.pi * Q ^ (α * (1 - α)) / (α * (1 - α)))
        = (4 * (2 * M) ^ α * (2 * H) ^ (1 - α) * (4 * Real.pi / (α * (1 - α))) * δ ^ α)
            * Q ^ (α * (1 - α)) := by ring
      _ ≤ (4 * (2 * M) ^ α * (2 * H) ^ (1 - α) * (4 * Real.pi / (α * (1 - α))) * δ ^ α)
            * P ^ (α * (1 - α)) := mul_le_mul_of_nonneg_left hQp hC
      _ = 4 * (2 * M) ^ α * (2 * H) ^ (1 - α) *
            (4 * Real.pi * P ^ (α * (1 - α)) / (α * (1 - α))) * δ ^ α := by ring
  have hδle : δ ≤ max 1 S * δ ^ α := by
    rcases eq_or_lt_of_le hδ with hδ0 | hδpos
    · rw [← hδ0, Real.zero_rpow hα.ne']
      simp
    · have hsplit : δ = δ ^ α * δ ^ (1 - α) := by
        rw [eq_comm, ← Real.rpow_add hδpos α (1 - α), show α + (1 - α) = 1 by ring,
          Real.rpow_one]
      have hle : δ ^ (1 - α) ≤ max 1 S := by
        rcases le_total δ 1 with hd1 | hd1
        · calc δ ^ (1 - α) ≤ 1 := Real.rpow_le_one hδ hd1 (by linarith)
            _ ≤ max 1 S := le_max_left _ _
        · calc δ ^ (1 - α) ≤ δ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
            _ = δ := Real.rpow_one δ
            _ ≤ S := hδS
            _ ≤ max 1 S := le_max_right _ _
      calc δ = δ ^ α * δ ^ (1 - α) := hsplit
        _ ≤ δ ^ α * max 1 S := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hδ _)
        _ = max 1 S * δ ^ α := by ring
  have hB : (4 * Real.pi / 3) * (M * δ) ≤ (4 * Real.pi / 3) * (M * max 1 S) * δ ^ α := by
    have hcoef : 0 ≤ (4 * Real.pi / 3) * M := by positivity
    calc (4 * Real.pi / 3) * (M * δ) = ((4 * Real.pi / 3) * M) * δ := by ring
      _ ≤ ((4 * Real.pi / 3) * M) * (max 1 S * δ ^ α) := mul_le_mul_of_nonneg_left hδle hcoef
      _ = (4 * Real.pi / 3) * (M * max 1 S) * δ ^ α := by ring
  exact le_trans (add_le_add hA hB) (le_of_eq (by ring))

end Work.CoreResiduals.BiotSavart
