import Mathlib

namespace Work.Horn.FatouQ

/-- For `θ < 1` and `c ≥ 0`, the quantity `c * a ^ θ` is eventually dominated by `a`.
This is the elementary fact that `x ↦ x ^ θ` grows slower than linearly when `θ < 1`. -/
lemma rpow_linear_bound {θ c : ℝ} (hθ : θ < 1) (hc : 0 ≤ c) :
    ∃ A : ℝ, ∀ a : ℝ, A ≤ a → c * a ^ θ ≤ a := by
  have he : 0 < 1 - θ := by linarith
  refine ⟨max 1 (c ^ ((1 - θ)⁻¹)), fun a ha => ?_⟩
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  have hca : c ^ ((1 - θ)⁻¹) ≤ a := le_trans (le_max_right _ _) ha
  have hbase : 0 ≤ c ^ ((1 - θ)⁻¹) := Real.rpow_nonneg hc _
  have h1 : c ≤ a ^ (1 - θ) := by
    have h2 := Real.rpow_le_rpow hbase hca he.le
    rw [← Real.rpow_mul hc, inv_mul_cancel₀ (ne_of_gt he), Real.rpow_one] at h2
    exact h2
  calc c * a ^ θ ≤ a ^ (1 - θ) * a ^ θ :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt ha0) θ)
    _ = a ^ ((1 - θ) + θ) := by rw [Real.rpow_add ha0]
    _ = a := by rw [show (1 : ℝ) - θ + θ = 1 by ring, Real.rpow_one]

theorem exists_threshold_rpow_interval
    {θ K L b : ℝ} (hθ : θ < 1) (hK : 0 ≤ K) (hL : 0 ≤ L) (hb : 0 ≤ b) :
    ∃ A : ℝ, ∀ a s : ℝ, A ≤ a → a ≤ s → s ≤ a + b → K * s ^ θ + L ≤ a := by
  by_cases hθ0 : θ ≤ 0
  · -- sublinear exponent: `s ^ θ ≤ a ^ θ ≤ 1`
    refine ⟨max 1 (K + L), fun a s ha has _ => ?_⟩
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
    have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
    have hKL : K + L ≤ a := le_trans (le_max_right _ _) ha
    have hsθ : s ^ θ ≤ a ^ θ := Real.rpow_le_rpow_of_nonpos ha0 has hθ0
    have haθ : a ^ θ ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le ha1 hθ0
      simpa [Real.rpow_zero] using h
    have hKs : K * s ^ θ ≤ K :=
      calc K * s ^ θ ≤ K * a ^ θ := mul_le_mul_of_nonneg_left hsθ hK
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left haθ hK
        _ = K := mul_one K
    linarith
  · -- positive exponent: `s ^ θ ≤ (a + b) ^ θ ≤ (2a) ^ θ = 2 ^ θ a ^ θ`
    have hθpos : 0 < θ := not_le.mp hθ0
    obtain ⟨A₁, hA₁⟩ := rpow_linear_bound hθ (c := 2 * (K * 2 ^ θ))
      (by positivity)
    refine ⟨max A₁ (max (max b (2 * L)) 1), fun a s ha has hsa => ?_⟩
    have hA₁a : A₁ ≤ a := le_trans (le_max_left _ _) ha
    have hba : b ≤ a :=
      le_trans (le_trans (le_max_left b (2 * L)) (le_max_left (max b (2 * L)) 1))
        (le_max_right A₁ (max (max b (2 * L)) 1)) |>.trans ha
    have h2La : 2 * L ≤ a :=
      le_trans (le_trans (le_max_right b (2 * L)) (le_max_left (max b (2 * L)) 1))
        (le_max_right A₁ (max (max b (2 * L)) 1)) |>.trans ha
    have h1a : (1 : ℝ) ≤ a :=
      le_trans (le_max_right (max b (2 * L)) 1) (le_max_right A₁ (max (max b (2 * L)) 1))
        |>.trans ha
    have ha0 : 0 < a := lt_of_lt_of_le one_pos h1a
    have hs0 : 0 ≤ s := le_trans (le_of_lt ha0) has
    have hab0 : 0 ≤ a + b := by linarith
    have hsθ : s ^ θ ≤ (a + b) ^ θ := Real.rpow_le_rpow hs0 hsa hθpos.le
    have hstep : (a + b) ^ θ ≤ (2 * a) ^ θ :=
      Real.rpow_le_rpow hab0 (by linarith) hθpos.le
    have hmul : (2 * a) ^ θ = 2 ^ θ * a ^ θ := Real.mul_rpow (by norm_num) (le_of_lt ha0)
    have hKs : K * s ^ θ ≤ (K * 2 ^ θ) * a ^ θ :=
      calc K * s ^ θ ≤ K * (a + b) ^ θ := mul_le_mul_of_nonneg_left hsθ hK
        _ ≤ K * (2 * a) ^ θ := mul_le_mul_of_nonneg_left hstep hK
        _ = K * (2 ^ θ * a ^ θ) := by rw [hmul]
        _ = (K * 2 ^ θ) * a ^ θ := by ring
    have hca : (K * 2 ^ θ) * a ^ θ ≤ a / 2 := by
      have := hA₁ a hA₁a
      linarith
    linarith

end Work.Horn.FatouQ
