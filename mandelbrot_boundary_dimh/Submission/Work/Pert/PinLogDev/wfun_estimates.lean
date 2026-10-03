import Mathlib

namespace Work.Pert.PinLogDev

theorem wfun_estimates {u : ℂ → ℂ} {σ : ℂ} {r M θu : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hθu : 0 < θu)
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hTay : ∀ t : ℂ, ‖t‖ ≤ θu → ‖u t - u 0 - deriv u 0 * t‖ ≤ M * ‖t‖ ^ 2)
    (hH0 : 1 - σ * u 0 ≠ 0) :
    ∃ c₁ c₂ θ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ 0 < θ ∧
      ∀ t : ℂ, ‖t‖ ≤ θ →
        ‖(1 - σ * u t / (1 + t * u t)) / (1 - σ * u 0) - 1‖ ≤ c₁ * ‖t‖ ∧
        ‖((1 - σ * u t / (1 + t * u t)) / (1 - σ * u 0) - 1)
            - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖ ≤ c₂ * ‖t‖ ^ 2 := by
  set u0 : ℂ := u 0 with hu0
  set u1 : ℂ := deriv u 0 with hu1
  have hH0' : 1 - σ * u0 ≠ 0 := by rw [hu0]; exact hH0
  have hTay' : ∀ t : ℂ, ‖t‖ ≤ θu → ‖u t - u0 - u1 * t‖ ≤ M * ‖t‖ ^ 2 := by
    intro t ht; rw [hu0, hu1]; exact hTay t ht
  set S : ℝ := ‖u0‖ + ‖u1‖ + M with hS
  have hSnn : 0 ≤ S := by
    rw [hS]; have h1 := norm_nonneg u0; have h2 := norm_nonneg u1; linarith [hM]
  have hS1 : 0 < S + 1 := by linarith
  set T : ℝ := min θu (min 1 (1 / (2 * (S + 1)))) with hT
  have hTpos : 0 < T := by
    rw [hT]
    exact lt_min hθu (lt_min one_pos (one_div_pos.mpr (by linarith)))
  have hTleθu : T ≤ θu := by rw [hT]; exact min_le_left _ _
  have hTle1 : T ≤ 1 := by
    rw [hT]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hTleS : T ≤ 1 / (2 * (S + 1)) := by
    rw [hT]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hTS : T * (S + 1) ≤ 1 / 2 := by
    calc T * (S + 1) ≤ (1 / (2 * (S + 1))) * (S + 1) :=
          mul_le_mul_of_nonneg_right hTleS hS1.le
      _ = 1 / 2 := by field_simp
  have hD0pos : 0 < ‖(1 : ℂ) - σ * u0‖ := norm_pos_iff.mpr hH0'
  set C1 : ℝ := 2 * ‖σ‖ * (M + ‖u1‖ + ‖u0‖ * (‖u0‖ + 1)) / ‖(1 : ℂ) - σ * u0‖ with hC1
  set C2 : ℝ := 2 * ‖σ‖ * (M + ‖u0‖ * ‖u1‖ + ‖u0‖ * M
      + ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1)) / ‖(1 : ℂ) - σ * u0‖ with hC2
  refine ⟨C1, C2, T, ?_, ?_, hTpos, ?_⟩
  · rw [hC1]; exact div_nonneg (by positivity) (norm_nonneg _)
  · rw [hC2]; exact div_nonneg (by positivity) (norm_nonneg _)
  · intro t ht
    have httu : ‖t‖ ≤ θu := le_trans ht hTleθu
    have ht1 : ‖t‖ ≤ 1 := le_trans ht hTle1
    have hη : ‖u t - u0 - u1 * t‖ ≤ M * ‖t‖ ^ 2 := hTay' t httu
    have hM2 : M * ‖t‖ ^ 2 ≤ M * ‖t‖ := by
      have h : ‖t‖ ^ 2 ≤ ‖t‖ := by
        have h1 : ‖t‖ * ‖t‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left ht1 (norm_nonneg t)
        simpa [pow_two] using h1
      exact mul_le_mul_of_nonneg_left h hM.le
    have hMS : M + ‖u1‖ ≤ S + 1 := by
      rw [hS]; have h1 := norm_nonneg u0; linarith
    have hM1 : M * ‖t‖ + ‖u1‖ * ‖t‖ ≤ 1 / 2 := by
      have h1 : (M + ‖u1‖) * ‖t‖ ≤ (S + 1) * ‖t‖ :=
        mul_le_mul_of_nonneg_right hMS (norm_nonneg t)
      have h2 : (S + 1) * ‖t‖ ≤ (S + 1) * T := mul_le_mul_of_nonneg_left ht hS1.le
      have h3 : (S + 1) * T ≤ 1 / 2 := by rw [mul_comm]; exact hTS
      have h4 : (M + ‖u1‖) * ‖t‖ = M * ‖t‖ + ‖u1‖ * ‖t‖ := by ring
      linarith [h1, h2, h3, h4]
    have hut1 : ‖u t‖ ≤ ‖u0‖ + 1 := by
      have h1 : ‖u t‖ ≤ ‖u t - u0 - u1 * t‖ + ‖u0‖ + ‖u1‖ * ‖t‖ := by
        have ha := norm_add_le ((u t - u0 - u1 * t) + u0) (u1 * t)
        have hb := norm_add_le (u t - u0 - u1 * t) u0
        have hc : ‖u1 * t‖ = ‖u1‖ * ‖t‖ := norm_mul _ _
        calc ‖u t‖ = ‖(u t - u0 - u1 * t) + u0 + u1 * t‖ := by congr 1; ring
          _ ≤ ‖u t - u0 - u1 * t‖ + ‖u0‖ + ‖u1‖ * ‖t‖ := by
              linarith [ha, hb, hc]
      linarith [h1, hη, hM2, hM1, norm_nonneg t]
    have hTN : T * (‖u0‖ + 1) ≤ 1 / 2 := by
      have hN : ‖u0‖ + 1 ≤ S + 1 := by rw [hS]; have h1 := norm_nonneg u1; linarith [hM]
      have h1 : T * (‖u0‖ + 1) ≤ (1 / (2 * (S + 1))) * (‖u0‖ + 1) :=
        mul_le_mul_of_nonneg_right hTleS (by positivity)
      have h2 : (1 / (2 * (S + 1))) * (‖u0‖ + 1) ≤ (1 / (2 * (S + 1))) * (S + 1) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      have h3 : (1 / (2 * (S + 1))) * (S + 1) = 1 / 2 := by field_simp
      linarith
    have htu : ‖t * u t‖ ≤ 1 / 2 := by
      rw [norm_mul]
      calc ‖t‖ * ‖u t‖ ≤ ‖t‖ * (‖u0‖ + 1) := mul_le_mul_of_nonneg_left hut1 (norm_nonneg t)
        _ ≤ T * (‖u0‖ + 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ ≤ 1 / 2 := hTN
    have hw_ne : 1 + t * u t ≠ 0 := by
      intro h
      have h1 : ‖t * u t‖ = 1 := by
        have h2 : t * u t = -1 := eq_neg_of_add_eq_zero_right h
        rw [h2, norm_neg, norm_one]
      linarith [htu, h1]
    have hw_norm : (1 : ℝ) / 2 ≤ ‖1 + t * u t‖ := by
      have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + t * u t‖ + ‖t * u t‖ := by
        have h := norm_add_le (1 + t * u t) (-(t * u t))
        have h2 : (1 + t * u t) + -(t * u t) = 1 := by ring
        rw [h2, norm_neg] at h
        simpa using h
      simp only [norm_one] at h1
      linarith [htu]
    have hcube : ‖t‖ ^ 3 ≤ ‖t‖ ^ 2 := by
      have h1 : ‖t‖ ^ 3 = ‖t‖ ^ 2 * ‖t‖ := by ring
      rw [h1]
      calc ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = ‖t‖ ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · have hid1 : (1 - σ * u t / (1 + t * u t)) / (1 - σ * u0) - 1
          = σ * (u0 - u t + u0 * (t * u t)) / ((1 + t * u t) * (1 - σ * u0)) := by
        rw [mul_comm t (u t)] at hw_ne
        field_simp
        ring
      have hE : ‖u0 - u t + u0 * (t * u t)‖
          ≤ (M + ‖u1‖ + ‖u0‖ * (‖u0‖ + 1)) * ‖t‖ := by
        have hsplit : u0 - u t + u0 * (t * u t)
            = -(u t - u0 - u1 * t) - u1 * t + u0 * (t * u t) := by ring
        rw [hsplit]
        have htri : ‖-(u t - u0 - u1 * t) - u1 * t + u0 * (t * u t)‖
            ≤ ‖u t - u0 - u1 * t‖ + ‖u1‖ * ‖t‖ + ‖u0 * (t * u t)‖ := by
          have ha := norm_add_le (-(u t - u0 - u1 * t) - u1 * t) (u0 * (t * u t))
          have hb := norm_sub_le (-(u t - u0 - u1 * t)) (u1 * t)
          have e1 : ‖-(u t - u0 - u1 * t)‖ = ‖u t - u0 - u1 * t‖ := norm_neg _
          have e2 : ‖u1 * t‖ = ‖u1‖ * ‖t‖ := norm_mul _ _
          linarith [ha, hb, e1, e2, norm_nonneg (u0 * (t * u t)), norm_nonneg (u1 * t)]
        have h4 : ‖u0 * (t * u t)‖ ≤ ‖u0‖ * (‖t‖ * (‖u0‖ + 1)) := by
          rw [norm_mul]
          have h5 : ‖t * u t‖ ≤ ‖t‖ * (‖u0‖ + 1) := by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left hut1 (norm_nonneg t)
          exact mul_le_mul_of_nonneg_left h5 (norm_nonneg u0)
        have htarget : (M + ‖u1‖ + ‖u0‖ * (‖u0‖ + 1)) * ‖t‖
            = M * ‖t‖ + ‖u1‖ * ‖t‖ + ‖u0‖ * (‖t‖ * (‖u0‖ + 1)) := by ring
        rw [htarget]
        linarith [htri, hη, hM2, h4]
      rw [hid1, norm_div, norm_mul, norm_mul]
      have hden : (1 / 2) * ‖(1 : ℂ) - σ * u0‖ ≤ ‖1 + t * u t‖ * ‖(1 : ℂ) - σ * u0‖ :=
        mul_le_mul_of_nonneg_right hw_norm hD0pos.le
      calc ‖σ‖ * ‖u0 - u t + u0 * (t * u t)‖ / (‖1 + t * u t‖ * ‖(1 : ℂ) - σ * u0‖)
          ≤ ‖σ‖ * ‖u0 - u t + u0 * (t * u t)‖ / ((1 / 2) * ‖(1 : ℂ) - σ * u0‖) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith [hD0pos]) hden
        _ ≤ ‖σ‖ * ((M + ‖u1‖ + ‖u0‖ * (‖u0‖ + 1)) * ‖t‖)
              / ((1 / 2) * ‖(1 : ℂ) - σ * u0‖) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE (norm_nonneg σ)) (by linarith [hD0pos])
        _ = C1 * ‖t‖ := by rw [hC1]; field_simp
    · have hid2 : (1 - σ * u t / (1 + t * u t)) / (1 - σ * u0) - 1
            - (σ * (u0 ^ 2 - u1) / (1 - σ * u0)) * t
          = σ * ((u0 - u t + u0 * (t * u t)) - (u0 ^ 2 - u1) * t * (1 + t * u t))
              / ((1 - σ * u0) * (1 + t * u t)) := by
        rw [mul_comm t (u t)] at hw_ne
        field_simp
        ring
      have hG : ‖(u0 - u t + u0 * (t * u t)) - (u0 ^ 2 - u1) * t * (1 + t * u t)‖
          ≤ (M + ‖u0‖ * ‖u1‖ + ‖u0‖ * M + ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1)) * ‖t‖ ^ 2 := by
        have hsplit : (u0 - u t + u0 * (t * u t)) - (u0 ^ 2 - u1) * t * (1 + t * u t)
            = -(u t - u0 - u1 * t) + u0 * u1 * t ^ 2 + u0 * t * (u t - u0 - u1 * t)
              - (u0 ^ 2 - u1) * (t ^ 2 * u t) := by ring
        rw [hsplit]
        have htri3 : ∀ a b c : ℂ, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
          intro a b c
          have ha := norm_add_le (a + b) c
          have hb := norm_add_le a b
          linarith [norm_nonneg c, norm_nonneg (a + b)]
        have hA : ‖-(u t - u0 - u1 * t) + u0 * u1 * t ^ 2 + u0 * t * (u t - u0 - u1 * t)
            - (u0 ^ 2 - u1) * (t ^ 2 * u t)‖
            ≤ ‖u t - u0 - u1 * t‖ + ‖u0 * u1 * t ^ 2‖ + ‖u0 * t * (u t - u0 - u1 * t)‖
              + ‖(u0 ^ 2 - u1) * (t ^ 2 * u t)‖ := by
          have ha := norm_sub_le
            (-(u t - u0 - u1 * t) + u0 * u1 * t ^ 2 + u0 * t * (u t - u0 - u1 * t))
            ((u0 ^ 2 - u1) * (t ^ 2 * u t))
          have hb := htri3 (-(u t - u0 - u1 * t)) (u0 * u1 * t ^ 2)
            (u0 * t * (u t - u0 - u1 * t))
          have e1 : ‖-(u t - u0 - u1 * t)‖ = ‖u t - u0 - u1 * t‖ := norm_neg _
          rw [e1] at hb
          linarith [ha, hb, norm_nonneg ((u0 ^ 2 - u1) * (t ^ 2 * u t))]
        have hT2 : ‖u0 * u1 * t ^ 2‖ = ‖u0‖ * ‖u1‖ * ‖t‖ ^ 2 := by
          simp only [norm_mul, norm_pow]
        have hT3 : ‖u0 * t * (u t - u0 - u1 * t)‖ ≤ ‖u0‖ * M * ‖t‖ ^ 2 := by
          rw [norm_mul, norm_mul]
          calc ‖u0‖ * ‖t‖ * ‖u t - u0 - u1 * t‖
              ≤ ‖u0‖ * ‖t‖ * (M * ‖t‖ ^ 2) := mul_le_mul_of_nonneg_left hη (by positivity)
            _ = ‖u0‖ * M * ‖t‖ ^ 3 := by ring
            _ ≤ ‖u0‖ * M * ‖t‖ ^ 2 := mul_le_mul_of_nonneg_left hcube (by positivity)
        have hT4 : ‖(u0 ^ 2 - u1) * (t ^ 2 * u t)‖ ≤ ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1) * ‖t‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow]
          calc ‖u0 ^ 2 - u1‖ * (‖t‖ ^ 2 * ‖u t‖)
              ≤ ‖u0 ^ 2 - u1‖ * (‖t‖ ^ 2 * (‖u0‖ + 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hut1 (by positivity))
                  (norm_nonneg _)
            _ = ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1) * ‖t‖ ^ 2 := by ring
        have htarget : (M + ‖u0‖ * ‖u1‖ + ‖u0‖ * M + ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1)) * ‖t‖ ^ 2
            = M * ‖t‖ ^ 2 + ‖u0‖ * ‖u1‖ * ‖t‖ ^ 2 + ‖u0‖ * M * ‖t‖ ^ 2
              + ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1) * ‖t‖ ^ 2 := by ring
        rw [htarget]
        linarith [hA, hη, hT2, hT3, hT4]
      rw [hid2, norm_div, norm_mul, norm_mul]
      have hden2 : (1 / 2) * ‖(1 : ℂ) - σ * u0‖
          ≤ ‖(1 : ℂ) - σ * u0‖ * ‖1 + t * u t‖ := by
        calc (1 / 2) * ‖(1 : ℂ) - σ * u0‖ ≤ ‖1 + t * u t‖ * ‖(1 : ℂ) - σ * u0‖ :=
              mul_le_mul_of_nonneg_right hw_norm hD0pos.le
          _ = ‖(1 : ℂ) - σ * u0‖ * ‖1 + t * u t‖ := by ring
      calc ‖σ‖ * ‖(u0 - u t + u0 * (t * u t)) - (u0 ^ 2 - u1) * t * (1 + t * u t)‖
              / (‖(1 : ℂ) - σ * u0‖ * ‖1 + t * u t‖)
          ≤ ‖σ‖ * ‖(u0 - u t + u0 * (t * u t)) - (u0 ^ 2 - u1) * t * (1 + t * u t)‖
              / ((1 / 2) * ‖(1 : ℂ) - σ * u0‖) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith [hD0pos]) hden2
        _ ≤ ‖σ‖ * ((M + ‖u0‖ * ‖u1‖ + ‖u0‖ * M + ‖u0 ^ 2 - u1‖ * (‖u0‖ + 1)) * ‖t‖ ^ 2)
              / ((1 / 2) * ‖(1 : ℂ) - σ * u0‖) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hG (norm_nonneg σ)) (by linarith [hD0pos])
        _ = C2 * ‖t‖ ^ 2 := by rw [hC2]; field_simp

end Work.Pert.PinLogDev
