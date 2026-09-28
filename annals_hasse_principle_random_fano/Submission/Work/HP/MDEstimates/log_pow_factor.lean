import Mathlib

namespace Work.HP.MDEstimates

/-- Auxiliary identity: for `x > 0`, `2 ^ (log x / log 2) = x`. -/
private lemma two_rpow_log_div (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ (Real.log x / Real.log 2) = x := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [mul_div_assoc', mul_div_cancel_left₀ _ h2]
  exact Real.exp_log hx

theorem log_pow_factor (KM : ℝ) (hKM : 1 ≤ KM) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Δ : ℝ) (N : ℕ), 1 ≤ Δ →
      N ≤ ⌈Real.logb 2 (8 * KM * (Δ + 1))⌉₊ →
      (((N : ℝ) + 2) ^ 2 ≤ C * (Real.log (2 * Δ)) ^ 2) ∧
      ((2 : ℝ) ^ (((3 : ℝ) / 2) * (N : ℝ)) ≤ C * Δ ^ ((3 : ℝ) / 2)) ∧
      ((2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) ≤ C * Δ ^ ((7 : ℝ) / 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have trld : ∀ (x : ℝ), 0 < x → (2 : ℝ) ^ (Real.log x / Real.log 2) = x :=
    two_rpow_log_div
  set β : ℝ := 1 / Real.log 2 with hβ
  set a : ℝ := Real.log (8 * KM) / Real.log 2 + 1 with ha
  have hβpos : 0 < β := by rw [hβ]; positivity
  have ha1 : 1 ≤ a := by
    rw [ha]
    have : 0 ≤ Real.log (8 * KM) / Real.log 2 :=
      div_nonneg (Real.log_nonneg (by nlinarith)) (le_of_lt hlog2)
    linarith
  refine ⟨max (((a + 3) * β) ^ 2)
      (max ((2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1))) ((2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)))), ?_, ?_⟩
  · rw [lt_max_iff]; left
    exact pow_pos (mul_pos (by linarith) hβpos) 2
  · intro Δ N hΔ hN
    have hΔpos : 0 < Δ := by linarith
    have hLpos : 0 < Real.log (2 * Δ) := Real.log_pos (by linarith)
    have hlogmul : Real.log (8 * KM * (Δ + 1)) = Real.log (8 * KM) + Real.log (Δ + 1) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have hlogle : Real.log (Δ + 1) ≤ Real.log (2 * Δ) :=
      Real.log_le_log (by linarith) (by linarith)
    have hx_nonneg : 0 ≤ Real.logb 2 (8 * KM * (Δ + 1)) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg (by nlinarith)) (le_of_lt hlog2)
    have hNbound : (N : ℝ) ≤ a + β * Real.log (2 * Δ) := by
      have h1 : (N : ℝ) ≤ (⌈Real.logb 2 (8 * KM * (Δ + 1))⌉₊ : ℝ) := by exact_mod_cast hN
      have h2 : (⌈Real.logb 2 (8 * KM * (Δ + 1))⌉₊ : ℝ) <
          Real.logb 2 (8 * KM * (Δ + 1)) + 1 :=
        Nat.ceil_lt_add_one hx_nonneg
      have hx_le : Real.logb 2 (8 * KM * (Δ + 1)) ≤
          Real.log (8 * KM) / Real.log 2 + β * Real.log (2 * Δ) := by
        rw [Real.logb, hlogmul]
        have step : (Real.log (8 * KM) + Real.log (Δ + 1)) / Real.log 2 ≤
            (Real.log (8 * KM) + Real.log (2 * Δ)) / Real.log 2 :=
          div_le_div_of_nonneg_right (by linarith) (le_of_lt hlog2)
        refine le_trans step ?_
        rw [add_div]
        have hthis : Real.log (2 * Δ) / Real.log 2 = β * Real.log (2 * Δ) := by
          rw [hβ]; ring
        rw [hthis]
      rw [ha]
      linarith
    have hβL1 : 1 ≤ β * Real.log (2 * Δ) := by
      have hLge : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
      have hthis : β * Real.log (2 * Δ) = Real.log (2 * Δ) / Real.log 2 := by
        rw [hβ, one_div_mul_eq_div]
      rw [hthis, le_div_iff₀ hlog2]
      linarith
    have hpow1 : (2 : ℝ) ^ (N : ℝ) ≤ (2 : ℝ) ^ (a + 1) * Δ := by
      have h1 : (2 : ℝ) ^ (N : ℝ) ≤ (2 : ℝ) ^ (a + β * Real.log (2 * Δ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hNbound
      have h2 : (2 : ℝ) ^ (a + β * Real.log (2 * Δ)) = (2 : ℝ) ^ (a + 1) * Δ := by
        rw [Real.rpow_add (by norm_num)]
        have h3 : (2 : ℝ) ^ (β * Real.log (2 * Δ)) = 2 * Δ := by
          have hthis : β * Real.log (2 * Δ) = Real.log (2 * Δ) / Real.log 2 := by
            rw [hβ, one_div_mul_eq_div]
          rw [hthis]; exact trld (2 * Δ) (by linarith)
        rw [h3]
        have h4 : (2 : ℝ) ^ (a + 1) = (2 : ℝ) ^ a * 2 := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
        rw [h4]; ring
      rw [h2] at h1; exact h1
    have hlog_claim : ((N : ℝ) + 2) ^ 2 ≤ (((a + 3) * β) ^ 2) * (Real.log (2 * Δ)) ^ 2 := by
      have hA : (N : ℝ) + 2 ≤ (a + 3) * β * Real.log (2 * Δ) := by
        have h1 : (N : ℝ) + 2 ≤ a + β * Real.log (2 * Δ) + 2 := by linarith
        have h2 : a + β * Real.log (2 * Δ) + 2 ≤ (a + 3) * β * Real.log (2 * Δ) := by
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ a + 2 by linarith)
            (show (0 : ℝ) ≤ β * Real.log (2 * Δ) - 1 by linarith)]
        linarith
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ) + 2) hA 2
      have he : ((a + 3) * β * Real.log (2 * Δ)) ^ 2 =
          (((a + 3) * β) ^ 2) * (Real.log (2 * Δ)) ^ 2 := by ring
      rw [he] at hp; exact hp
    have h3bound : (2 : ℝ) ^ ((3 : ℝ) / 2 * (N : ℝ)) ≤
        ((2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1))) * Δ ^ ((3 : ℝ) / 2) := by
      have he : (2 : ℝ) ^ ((3 : ℝ) / 2 * (N : ℝ)) = ((2 : ℝ) ^ (N : ℝ)) ^ ((3 : ℝ) / 2) := by
        rw [show (3 : ℝ) / 2 * (N : ℝ) = (N : ℝ) * ((3 : ℝ) / 2) by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [he]
      have step : ((2 : ℝ) ^ (N : ℝ)) ^ ((3 : ℝ) / 2) ≤ ((2 : ℝ) ^ (a + 1) * Δ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) N) hpow1 (by norm_num)
      refine le_trans step ?_
      rw [Real.mul_rpow (by positivity) (le_of_lt hΔpos)]
      have he2 : ((2 : ℝ) ^ (a + 1)) ^ ((3 : ℝ) / 2) = (2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring
      rw [he2]
    have h7bound : (2 : ℝ) ^ ((7 : ℝ) / 2 * (N : ℝ)) ≤
        ((2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1))) * Δ ^ ((7 : ℝ) / 2) := by
      have he : (2 : ℝ) ^ ((7 : ℝ) / 2 * (N : ℝ)) = ((2 : ℝ) ^ (N : ℝ)) ^ ((7 : ℝ) / 2) := by
        rw [show (7 : ℝ) / 2 * (N : ℝ) = (N : ℝ) * ((7 : ℝ) / 2) by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [he]
      have step : ((2 : ℝ) ^ (N : ℝ)) ^ ((7 : ℝ) / 2) ≤ ((2 : ℝ) ^ (a + 1) * Δ) ^ ((7 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) N) hpow1 (by norm_num)
      refine le_trans step ?_
      rw [Real.mul_rpow (by positivity) (le_of_lt hΔpos)]
      have he2 : ((2 : ℝ) ^ (a + 1)) ^ ((7 : ℝ) / 2) = (2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring
      rw [he2]
    refine ⟨?_, ?_, ?_⟩
    · have hC1le : (((a + 3) * β) ^ 2) ≤ max (((a + 3) * β) ^ 2)
          (max ((2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1))) ((2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)))) :=
        le_max_left _ _
      exact le_trans hlog_claim (mul_le_mul_of_nonneg_right hC1le (sq_nonneg _))
    · have hC2le : (2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1)) ≤ max (((a + 3) * β) ^ 2)
          (max ((2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1))) ((2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)))) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans h3bound (mul_le_mul_of_nonneg_right hC2le (Real.rpow_nonneg (le_of_lt hΔpos) _))
    · have hC3le : (2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)) ≤ max (((a + 3) * β) ^ 2)
          (max ((2 : ℝ) ^ ((3 : ℝ) / 2 * (a + 1))) ((2 : ℝ) ^ ((7 : ℝ) / 2 * (a + 1)))) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans h7bound (mul_le_mul_of_nonneg_right hC3le (Real.rpow_nonneg (le_of_lt hΔpos) _))

end Work.HP.MDEstimates
