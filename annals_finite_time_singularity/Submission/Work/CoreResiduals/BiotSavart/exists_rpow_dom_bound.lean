import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Pointwise domination of a singular Biot--Savart kernel power by a weight
`1 + ‖a‖^(c-3)`, uniformly for `‖x‖ ≤ X` and `δ ≤ ‖x - a‖`.

For the exponent `c - 3 ≥ 0` we use `‖x - a‖ ≤ (X+1) * (1 + ‖a‖)` and
`(1 + t)^p ≤ 2^p (1 + t^p)`; for `c - 3 ≤ 0` we use monotonicity of `t ↦ t^p`
together with `δ ≤ ‖x - a‖`. -/
theorem exists_rpow_dom_bound {C c X δ : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hX : 0 ≤ X) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x a : Work.LWP.R3), ‖x‖ ≤ X → δ ≤ ‖x - a‖ →
      4 * C * (‖x - a‖ : ℝ) ^ (c - 3) ≤ K * (1 + (‖a‖ : ℝ) ^ (c - 3)) := by
  have hc0 : (0 : ℝ) < c := hc
  by_cases h3 : 3 ≤ c
  · have hp : 0 ≤ c - 3 := by linarith
    refine ⟨4 * C * ((X + 1) ^ (c - 3) * (2:ℝ) ^ (c - 3)), ?_, ?_⟩
    · refine mul_nonneg (by linarith) (mul_nonneg ?_ ?_)
      · exact Real.rpow_nonneg (by linarith) _
      · exact Real.rpow_nonneg (by norm_num) _
    · intro x a hx hd
      have ht : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
      have hsub : ‖x - a‖ ≤ (X + 1) * (1 + ‖a‖) := by
        have h1 : ‖x - a‖ ≤ ‖x‖ + ‖a‖ := norm_sub_le x a
        have h2 : ‖x‖ + ‖a‖ ≤ X + ‖a‖ := by linarith
        have h3' : X + ‖a‖ ≤ (X + 1) * (1 + ‖a‖) := by nlinarith
        linarith
      have hsp : ‖x - a‖ ^ (c - 3) ≤ ((X + 1) * (1 + ‖a‖)) ^ (c - 3) :=
        Real.rpow_le_rpow (norm_nonneg _) hsub hp
      rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ X + 1) (by linarith : (0:ℝ) ≤ 1 + ‖a‖)] at hsp
      have h1t : (1 + ‖a‖) ^ (c - 3) ≤ (2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)) := by
        by_cases ht1 : ‖a‖ ≤ 1
        · have hle : (1 + ‖a‖) ^ (c - 3) ≤ (2:ℝ) ^ (c - 3) :=
            Real.rpow_le_rpow (by linarith) (by linarith) hp
          exact le_trans hle (le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num) _)
            (by linarith [Real.rpow_nonneg ht (c-3)]))
        · have hle : (1 + ‖a‖) ^ (c - 3) ≤ ((2:ℝ) * ‖a‖) ^ (c - 3) :=
            Real.rpow_le_rpow (by linarith) (by linarith) hp
          rw [Real.mul_rpow (by norm_num) ht] at hle
          refine le_trans hle (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _))
          linarith [Real.rpow_nonneg ht (c-3)]
      have step : ‖x - a‖ ^ (c - 3) ≤
          (X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3))) :=
        calc ‖x - a‖ ^ (c - 3) ≤ (X + 1) ^ (c - 3) * (1 + ‖a‖) ^ (c - 3) := hsp
          _ ≤ (X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3))) :=
              mul_le_mul_of_nonneg_left h1t (Real.rpow_nonneg (by linarith) _)
      calc 4 * C * ‖x - a‖ ^ (c - 3)
          ≤ 4 * C * ((X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)))) :=
            mul_le_mul_of_nonneg_left step (by linarith)
        _ = 4 * C * ((X + 1) ^ (c - 3) * (2:ℝ) ^ (c - 3)) * (1 + ‖a‖ ^ (c - 3)) := by ring
  · have hp : c - 3 ≤ 0 := by linarith
    refine ⟨4 * C * δ ^ (c - 3), ?_, ?_⟩
    · exact mul_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hδ _))
    · intro x a hx hd
      have ht : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
      have hsp : ‖x - a‖ ^ (c - 3) ≤ δ ^ (c - 3) :=
        Real.rpow_le_rpow_of_nonpos hδ hd hp
      have h1 : 4 * C * ‖x - a‖ ^ (c - 3) ≤ 4 * C * δ ^ (c - 3) :=
        mul_le_mul_of_nonneg_left hsp (by linarith)
      have h2 : 4 * C * δ ^ (c - 3) ≤ 4 * C * δ ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)) :=
        le_mul_of_one_le_right (mul_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hδ _)))
          (by linarith [Real.rpow_nonneg ht (c-3)])
      exact le_trans h1 h2

end Work.CoreResiduals.BiotSavart
