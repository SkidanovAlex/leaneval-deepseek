import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

theorem v2_remainder_le {μ b d Q : ℕ} {ρ : ℝ} {t s₀ : Fin μ → ℝ}
    {PS : MvPolynomial (Fin (μ + 1)) ℝ}
    (hcoefsum : (∑ m ∈ PS.support, |PS.coeff m|)
      ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ))
    (hdeg : PS.totalDegree ≤ d) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hdiam : ‖t - s₀‖ ≤ ρ)
    (hlt : ‖t - s₀‖ ≤ Real.sqrt (μ : ℝ) * ρ) :
    (∑ m ∈ PS.support, |PS.coeff m|) * (((PS.totalDegree : ℕ) : ℝ) + 1) ^ (b + 1)
        * (max 1 ‖t - s₀‖) ^ (b + 1) * ‖t - s₀‖ ^ (b + 1) / ((((b + 1).factorial : ℕ) : ℝ))
      ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * ((d : ℝ) + 1) ^ (b + 1)
        * ((Real.sqrt (μ : ℝ) * ρ) ^ (b + 1)) / ((((b + 1).factorial : ℕ) : ℝ)) := by
  -- Since `‖t - s₀‖ ≤ ρ ≤ 1`, the factor `(max 1 ‖t - s₀‖)^(b+1)` is just `1`.
  have hx1 : ‖t - s₀‖ ≤ 1 := le_trans hdiam hρ1
  have hmax : max 1 ‖t - s₀‖ = 1 := max_eq_left hx1
  have hden : (0 : ℝ) < (((b + 1).factorial : ℕ) : ℝ) := by positivity
  rw [hmax, one_pow, mul_one]
  -- Cancel the common positive factor `(b+1)!`.
  rw [div_le_div_iff_of_pos_right hden]
  -- `totalDegree + 1 ≤ d + 1` and `‖t - s₀‖ ≤ √μ · ρ`, so each factor is bounded termwise.
  have htd : ((PS.totalDegree : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdeg
  have hA : (((PS.totalDegree : ℕ) : ℝ) + 1) ^ (b + 1) ≤ ((d : ℝ) + 1) ^ (b + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (b + 1)
  have hD : ‖t - s₀‖ ^ (b + 1) ≤ (Real.sqrt (μ : ℝ) * ρ) ^ (b + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hlt (b + 1)
  exact mul_le_mul (mul_le_mul hcoefsum hA (by positivity) (by positivity)) hD
    (by positivity) (by positivity)

end Work.WilkiesH.Interp
