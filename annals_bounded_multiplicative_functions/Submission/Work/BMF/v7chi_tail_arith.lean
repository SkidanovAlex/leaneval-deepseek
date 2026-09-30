import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The trivial bound for the far tail of the shift-difference series is uniformly bounded. -/
lemma v7chi_tail_arith : ∃ A : ℝ, 0 < A ∧ ∀ (σ t : ℝ), 3 ≤ |t| → 1 / 2 ≤ σ →
    ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ *
      ((Nat.ceil |t| * Nat.ceil |t| + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤ A := by
  refine ⟨4, by norm_num, ?_⟩
  intro σ t ht hσ
  have htpos : 0 < |t| := by linarith
  have hσpos : 0 < σ := by linarith
  -- abbreviate the ceiling
  set m : ℕ := Nat.ceil |t| with hm
  have hm_ge : |t| ≤ (m : ℝ) := by
    rw [hm]; exact Nat.le_ceil |t|
  -- value of the base of the power
  have hBval : ((m * m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) ^ 2 + 2 := by
    push_cast; ring
  have hBpos : 0 < ((m * m + 1 + 1 : ℕ) : ℝ) := by
    rw [hBval]; positivity
  have hB1 : 1 ≤ ((m * m + 1 + 1 : ℕ) : ℝ) := by
    rw [hBval]; nlinarith [sq_nonneg (m : ℝ)]
  -- the base dominates t ^ 2
  have hB_ge_tsq : t ^ 2 ≤ ((m * m + 1 + 1 : ℕ) : ℝ) := by
    rw [hBval]
    have hsquare : t ^ 2 ≤ (m : ℝ) ^ 2 := by
      have h1 : |t| ≤ (m : ℝ) := hm_ge
      have h2 : (0 : ℝ) ≤ |t| := abs_nonneg t
      have h3 : (0 : ℝ) ≤ (m : ℝ) := le_trans h2 h1
      calc t ^ 2 = |t| ^ 2 := by rw [sq_abs]
        _ ≤ (m : ℝ) ^ 2 := by nlinarith
    linarith
  -- exponent monotonicity
  have hstep1 : ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  -- B ^ (-1/2) = (sqrt B)⁻¹ ≤ 1/|t|
  have hsqrt_ge : |t| ≤ Real.sqrt (((m * m + 1 + 1 : ℕ) : ℝ)) := by
    have h := Real.sqrt_le_sqrt hB_ge_tsq
    rwa [Real.sqrt_sq_eq_abs] at h
  have hstep2 : ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / |t| := by
    rw [Real.rpow_neg (le_of_lt hBpos), ← Real.sqrt_eq_rpow, inv_eq_one_div]
    exact one_div_le_one_div_of_le htpos hsqrt_ge
  have hpow : ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 / |t| :=
    le_trans hstep1 hstep2
  have hPnonneg : 0 ≤ ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-σ) :=
    le_of_lt (Real.rpow_pos_of_pos hBpos _)
  -- the norm factor is bounded by 1 + 2|t|
  have hnorm : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ ≤ 1 + 2 * |t| := by
    have h1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + |t| := by
      have h0 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      have h2 : ‖(σ : ℂ)‖ = σ := by simp [abs_of_pos hσpos]
      have h3 : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
      rwa [h2, h3] at h0
    have h2 : (σ + |t|) / σ ≤ 1 + 2 * |t| := by
      rw [add_div, div_self (ne_of_gt hσpos)]
      have h3 : |t| / σ ≤ 2 * |t| := by
        rw [div_le_iff₀ hσpos]
        nlinarith [abs_nonneg t]
      linarith
    exact le_trans (div_le_div_of_nonneg_right h1 (le_of_lt hσpos)) h2
  -- combine
  calc
    ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ * ((m * m + 1 + 1 : ℕ) : ℝ) ^ (-σ)
        ≤ (1 + 2 * |t|) * (1 / |t|) :=
          mul_le_mul hnorm hpow hPnonneg (by positivity)
    _ ≤ 4 := by
          rw [mul_one_div, div_le_iff₀ htpos]
          nlinarith [abs_nonneg t]

end Work.BMF
