import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevA4Book

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- Product of three real bounds. -/
private lemma mul3_le {a b c A B C : ℝ} (h0a : 0 ≤ a) (h0b : 0 ≤ b) (h0c : 0 ≤ c)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) : a * b * c ≤ A * B * C := by
  have hA : 0 ≤ A := le_trans h0a ha
  have hB : 0 ≤ B := le_trans h0b hb
  exact mul_le_mul (mul_le_mul ha hb h0b hA) hc h0c (mul_nonneg hA hB)

/-- Product of four real bounds. -/
private lemma mul4_le {a b c d A B C D : ℝ} (h0a : 0 ≤ a) (h0b : 0 ≤ b) (h0c : 0 ≤ c)
    (h0d : 0 ≤ d) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    a * b * c * d ≤ A * B * C * D := by
  have hA : 0 ≤ A := le_trans h0a ha
  have hB : 0 ≤ B := le_trans h0b hb
  have hC : 0 ≤ C := le_trans h0c hc
  have h1 : a * b * c ≤ A * B * C := mul3_le h0a h0b h0c ha hb hc
  exact mul_le_mul h1 hd h0d (mul_nonneg (mul_nonneg hA hB) hC)

/-- Multiply a nonnegative product by `Q ≥ 1`. -/
private lemma prod_le_prod_mul {A B Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 1 ≤ Q) :
    A * B ≤ A * B * Q := by
  calc A * B = A * B * 1 := by ring
    _ ≤ A * B * Q := mul_le_mul_of_nonneg_left hQ (mul_nonneg hA hB)

/-- Multiply a nonnegative product by `Q ^ 2`, `Q ≥ 1`. -/
private lemma prod_le_prod_mul_sq {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 1 ≤ R) :
    A * B ≤ A * B * R ^ 2 := by
  have hR2 : (1:ℝ) ≤ R ^ 2 := one_le_pow₀ hR
  calc A * B = A * B * 1 := by ring
    _ ≤ A * B * R ^ 2 := mul_le_mul_of_nonneg_left hR2 (mul_nonneg hA hB)

/-- The constant multiplying `S ^ (2+N14) T^2 Q^2` in the first block bound. -/
private def KAc (C0 C6 : ℝ) : ℝ :=
  576 * C6 * 4 + 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)

/-- The constant multiplying `S ^ (2+N14) T^2 Q^2` in the second block bound. -/
private def KBc (C0 C2 C6 C14 Cj : ℝ) : ℝ :=
  24 * C2 * C14 * 4
    + C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj)
        + 96 * (2 + 6 / Real.pi) * (Cj + 240))
    + 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984))

/-- The constant multiplying `S ^ (2+N14) T^2 Q^2` in the third block bound. -/
private def KCc (C0 C2 C6 C14 Cj : ℝ) : ℝ :=
  (Cj + 720) * (C2 * C14 * 4 + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240)
    + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984))

private lemma KAc_nonneg {C0 C6 : ℝ} (h0 : 0 < C0) (h6 : 0 < C6) : 0 ≤ KAc C0 C6 := by
  rw [KAc]; positivity

private lemma KBc_nonneg {C0 C2 C6 C14 Cj : ℝ} (h0 : 0 < C0) (h2 : 0 < C2) (h6 : 0 < C6)
    (h14 : 0 < C14) (hj : 0 < Cj) : 0 ≤ KBc C0 C2 C6 C14 Cj := by
  rw [KBc]; positivity

private lemma KCc_nonneg {C0 C2 C6 C14 Cj : ℝ} (h0 : 0 < C0) (h2 : 0 < C2) (h6 : 0 < C6)
    (h14 : 0 < C14) (hj : 0 < Cj) : 0 ≤ KCc C0 C2 C6 C14 Cj := by
  rw [KCc]; positivity

/-- Product of five real bounds. -/
private lemma mul5_le {a b c d e A B C D E : ℝ} (h0a : 0 ≤ a) (h0b : 0 ≤ b) (h0c : 0 ≤ c)
    (h0d : 0 ≤ d) (h0e : 0 ≤ e) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D)
    (he : e ≤ E) : a * b * c * d * e ≤ A * B * C * D * E := by
  have hA : 0 ≤ A := le_trans h0a ha
  have hB : 0 ≤ B := le_trans h0b hb
  have hC : 0 ≤ C := le_trans h0c hc
  have hD : 0 ≤ D := le_trans h0d hd
  have h1 : a * b * c * d ≤ A * B * C * D := mul4_le h0a h0b h0c h0d ha hb hc hd
  exact mul_le_mul h1 he h0e (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD)

theorem KdevA4plusBound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖(Work.Asymptotics.Compact.tailC)⁻¹ *
          ( (-576 * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2
              - 72 * ((τ : ℂ) * Work.Kernels.E6Fun τ
                    * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
                  + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2))
            - ( -24 * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                    / Work.Kernels.DeltaFun τ)
                + (τ : ℂ) * Work.Kernels.E6Fun τ
                    * (((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                          * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
                      - 48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
                          * (Work.Kernels.jInvariantFun τ - 240))
                - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                    * (((z : ℂ) ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ))
                          * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
                      - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)) )
            - (Work.Kernels.jInvariantFun τ - 720)
                * ( Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                      / Work.Kernels.DeltaFun τ
                  + (τ : ℂ) * Work.Kernels.E6Fun τ
                      * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                      * (Work.Kernels.jInvariantFun τ - 240)
                  - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                      * ((z : ℂ) ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ))
                      * (Work.Kernels.jInvariantFun τ - 984) ) )‖
          ≤ C * ((‖Work.Kernels.qParamFun τ‖)⁻¹) ^ 2 * (Work.Kernels.scale τ) ^ N
              * (1 + t) ^ M := by
  obtain ⟨C6, hC6, hE6b⟩ := kdevA4_norm_E6_le
  obtain ⟨Cj, hCj, hjb⟩ := kdevA4_norm_j_le
  obtain ⟨C0, hC0, hφ0b⟩ := kdevA4_norm_phi0_le
  obtain ⟨C2, hC2, hφ2b⟩ := kdevA4_norm_phi2_le
  obtain ⟨C14, N14, hC14, hN14, hE14b⟩ := kdevA4_norm_E14_div_Delta_le
  have hKA0 : (0 : ℝ) ≤ KAc C0 C6 := KAc_nonneg hC0 hC6
  have hKB0 : (0 : ℝ) ≤ KBc C0 C2 C6 C14 Cj := KBc_nonneg hC0 hC2 hC6 hC14 hCj
  have hKC0 : (0 : ℝ) ≤ KCc C0 C2 C6 C14 Cj := KCc_nonneg hC0 hC2 hC6 hC14 hCj
  refine ⟨‖Work.Asymptotics.Compact.tailC⁻¹‖ *
      (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj) + 1,
    2 + N14, 2, ?_, ?_, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ ‖Work.Asymptotics.Compact.tailC⁻¹‖ *
        (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj) :=
      mul_nonneg (norm_nonneg _) (by linarith)
    linarith
  · linarith
  · norm_num
  · intro τ z t hτ ht hz1 hz2 hzim
    set S : ℝ := Work.Kernels.scale τ with hSdef
    set T : ℝ := 1 + t with hTdef
    set Q : ℝ := (‖Work.Kernels.qParamFun τ‖)⁻¹ with hQdef
    set AA : ℂ := (-576 * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2
              - 72 * ((τ : ℂ) * Work.Kernels.E6Fun τ
                    * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
                  + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)) with hAA
    set BB : ℂ := ( -24 * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                    / Work.Kernels.DeltaFun τ)
                + (τ : ℂ) * Work.Kernels.E6Fun τ
                    * (((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                          * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
                      - 48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
                          * (Work.Kernels.jInvariantFun τ - 240))
                - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                    * (((z : ℂ) ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ))
                          * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
                      - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)) ) with hBB
    set CC : ℂ := (Work.Kernels.jInvariantFun τ - 720)
                * ( Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
                      / Work.Kernels.DeltaFun τ
                  + (τ : ℂ) * Work.Kernels.E6Fun τ
                      * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                      * (Work.Kernels.jInvariantFun τ - 240)
                  - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                      * ((z : ℂ) ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ))
                      * (Work.Kernels.jInvariantFun τ - 984) ) with hCC
    rw [show T ^ (2 : ℝ) = T ^ 2 from by rw [Real.rpow_two, pow_two]]
    have hS1 : (1 : ℝ) ≤ S := by rw [hSdef]; exact Work.Kernels.one_le_scale τ
    have hS0 : (0 : ℝ) ≤ S := le_trans zero_le_one hS1
    have hSpos : (0 : ℝ) < S := lt_of_lt_of_le zero_lt_one hS1
    have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; linarith [hτ.2, ht]
    have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
    have hTleT2 : T ≤ T ^ 2 := by
      have h := pow_le_pow_right₀ hT1 (show (1 : ℕ) ≤ 2 by norm_num)
      simpa using h
    have h6pi : (0 : ℝ) < 6 / Real.pi := by positivity
    have hQ1 : (1 : ℝ) ≤ Q := by
      rw [hQdef]
      have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ :=
        norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
      rw [one_le_inv₀ hqpos, Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, hτ.2]
    have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
    have hQ2 : (1 : ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ1
    have hQle : Q ≤ Q ^ 2 := by
      calc Q = Q * 1 := by ring
        _ ≤ Q * Q := mul_le_mul_of_nonneg_left hQ1 hQ0
        _ = Q ^ 2 := by ring
    have hSle : S ≤ S ^ (2 + N14) := by
      have h := Real.rpow_le_rpow_of_exponent_le hS1 (show (1 : ℝ) ≤ 2 + N14 by linarith [hN14])
      simpa using h
    have hτb : ‖(τ : ℂ)‖ ≤ S := by rw [hSdef]; exact Work.Kernels.coe_norm_le_scale τ
    have hτS : ‖(τ : ℂ)‖ ≤ S ^ (2 + N14) := le_trans hτb hSle
    have hE6 : ‖Work.Kernels.E6Fun τ‖ ≤ C6 := hE6b τ hτ
    have hE4 : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
    have hφ0 : ‖Work.Kernels.phi0 τ‖ ≤ C0 * S := by
      simpa only [← hSdef] using hφ0b τ hτ
    have hφ0S : ‖Work.Kernels.phi0 τ‖ ≤ C0 * S ^ (2 + N14) :=
      le_trans hφ0 (mul_le_mul_of_nonneg_left hSle hC0.le)
    have hφ2 : ‖Work.Kernels.phi2 τ‖ ≤ C2 * S ^ (2 : ℝ) := by
      have h := hφ2b τ hτ
      have he : (Work.Kernels.scale τ) ^ 2 = S ^ (2 : ℝ) := by
        rw [← hSdef, Real.rpow_two, pow_two]
      rw [he] at h
      exact h
    have hE14 : ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖ ≤ C14 * S ^ N14 * Q := by
      simpa only [← hSdef, ← hQdef] using hE14b τ hτ
    have hj : ‖Work.Kernels.jInvariantFun τ‖ ≤ Cj * Q := by
      simpa only [← hQdef] using hjb τ hτ
    have hzcn : ‖(z : ℂ)‖ ≤ 2 * T := by
      simpa only [← hTdef] using kdevA4_norm_z_le z t hz1 hz2 hzim
    have hz4T : ‖(z : ℂ)‖ ^ 2 ≤ 4 * T ^ 2 := by
      calc ‖(z : ℂ)‖ ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzcn 2
        _ = 4 * T ^ 2 := by ring
    have hzcq : ‖(z : ℂ)‖ ^ 2 ≤ 4 * T ^ 2 * Q ^ 2 := by
      calc ‖(z : ℂ)‖ ^ 2 ≤ 4 * T ^ 2 := hz4T
        _ = 4 * T ^ 2 * 1 := by ring
        _ ≤ 4 * T ^ 2 * Q ^ 2 := mul_le_mul_of_nonneg_left hQ2 (by positivity)
    have hcn : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hzcsub : ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ ≤ (2 + 6 / Real.pi) * T := by
      have h := norm_sub_le (z : ℂ) ((6 : ℂ) * Complex.I / (Real.pi : ℂ))
      rw [hcn] at h
      calc ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
          ≤ ‖(z : ℂ)‖ + 6 / Real.pi := h
        _ ≤ 2 * T + 6 / Real.pi := by linarith [hzcn]
        _ ≤ (2 + 6 / Real.pi) * T := by
            have h := mul_le_mul_of_nonneg_left hT1 h6pi.le
            have h' : 6 / Real.pi ≤ 6 / Real.pi * T := by simpa using h
            have he : (2 + 6 / Real.pi) * T = 2 * T + 6 / Real.pi * T := by ring
            rw [he]; linarith [h']
    have hzcsub2 : ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
        ≤ (2 + 6 / Real.pi) ^ 2 * T ^ 2 := by
      rw [norm_pow]
      calc ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ ^ 2
          ≤ ((2 + 6 / Real.pi) * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzcsub 2
        _ = (2 + 6 / Real.pi) ^ 2 * T ^ 2 := by ring
    have hzzc : ‖(z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))‖
        ≤ 2 * (2 + 6 / Real.pi) * T ^ 2 := by
      rw [norm_mul]
      calc ‖(z : ℂ)‖ * ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
          ≤ (2 * T) * ((2 + 6 / Real.pi) * T) :=
            mul_le_mul hzcn hzcsub (norm_nonneg _) (by linarith [hT1])
        _ = 2 * (2 + 6 / Real.pi) * T ^ 2 := by ring
    have hzsqcz : ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
        ≤ (4 + 12 / Real.pi) * T ^ 2 := by
      have h := norm_sub_le ((z : ℂ) ^ 2) ((6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
      rw [norm_pow, norm_mul, hcn] at h
      calc ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
          ≤ ‖(z : ℂ)‖ ^ 2 + 6 / Real.pi * ‖(z : ℂ)‖ := h
        _ ≤ (4 + 12 / Real.pi) * T ^ 2 := by
            have h1 : ‖(z : ℂ)‖ ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzcn 2
            rw [show (2 * T) ^ 2 = 4 * T ^ 2 by ring] at h1
            have h2 : 6 / Real.pi * ‖(z : ℂ)‖ ≤ 6 / Real.pi * (2 * T) :=
              mul_le_mul_of_nonneg_left hzcn h6pi.le
            rw [show 6 / Real.pi * (2 * T) = (12 / Real.pi) * T by ring] at h2
            have h3 : (12 / Real.pi) * T ≤ (12 / Real.pi) * T ^ 2 :=
              mul_le_mul_of_nonneg_left hTleT2 (by positivity)
            have he : (4 + 12 / Real.pi) * T ^ 2 = 4 * T ^ 2 + (12 / Real.pi) * T ^ 2 := by ring
            rw [he]; linarith [h1, h2, h3]
    have hj240 : ‖Work.Kernels.jInvariantFun τ - (240 : ℂ)‖ ≤ (Cj + 240) * Q := by
      have h := norm_sub_le (Work.Kernels.jInvariantFun τ) ((240 : ℂ))
      rw [Complex.norm_ofNat] at h
      have h240 : (240 : ℝ) ≤ 240 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ 240 by norm_num)
        simpa using h
      calc ‖Work.Kernels.jInvariantFun τ - (240 : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun τ‖ + 240 := h
        _ ≤ Cj * Q + 240 * Q := add_le_add hj h240
        _ = (Cj + 240) * Q := by ring
    have hj720 : ‖Work.Kernels.jInvariantFun τ - (720 : ℂ)‖ ≤ (Cj + 720) * Q := by
      have h := norm_sub_le (Work.Kernels.jInvariantFun τ) ((720 : ℂ))
      rw [Complex.norm_ofNat] at h
      have h720 : (720 : ℝ) ≤ 720 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ 720 by norm_num)
        simpa using h
      calc ‖Work.Kernels.jInvariantFun τ - (720 : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun τ‖ + 720 := h
        _ ≤ Cj * Q + 720 * Q := add_le_add hj h720
        _ = (Cj + 720) * Q := by ring
    have hj984 : ‖Work.Kernels.jInvariantFun τ - (984 : ℂ)‖ ≤ (Cj + 984) * Q := by
      have h := norm_sub_le (Work.Kernels.jInvariantFun τ) ((984 : ℂ))
      rw [Complex.norm_ofNat] at h
      have h984 : (984 : ℝ) ≤ 984 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ 984 by norm_num)
        simpa using h
      calc ‖Work.Kernels.jInvariantFun τ - (984 : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun τ‖ + 984 := h
        _ ≤ Cj * Q + 984 * Q := add_le_add hj h984
        _ = (Cj + 984) * Q := by ring
    have hK1 : ‖(-117360 : ℂ) - 24 * Work.Kernels.jInvariantFun τ‖
        ≤ (117360 + 24 * Cj) * Q := by
      have h := norm_sub_le ((-117360 : ℂ)) (24 * Work.Kernels.jInvariantFun τ)
      rw [norm_neg, Complex.norm_ofNat, norm_mul, Complex.norm_ofNat] at h
      have h2 : (24 : ℝ) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 24 * Cj * Q := by
        calc (24 : ℝ) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 24 * (Cj * Q) :=
              mul_le_mul_of_nonneg_left hj (by norm_num)
          _ = 24 * Cj * Q := by ring
      have h3 : (117360 : ℝ) ≤ 117360 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ 117360 by norm_num)
        simpa using h
      calc ‖(-117360 : ℂ) - 24 * Work.Kernels.jInvariantFun τ‖
          ≤ 117360 + 24 * ‖Work.Kernels.jInvariantFun τ‖ := h
        _ ≤ 117360 * Q + 24 * Cj * Q := add_le_add h3 h2
        _ = (117360 + 24 * Cj) * Q := by ring
    have hK2 : ‖(-314712 : ℂ) - 24 * Work.Kernels.jInvariantFun τ‖
        ≤ (314712 + 24 * Cj) * Q := by
      have h := norm_sub_le ((-314712 : ℂ)) (24 * Work.Kernels.jInvariantFun τ)
      rw [norm_neg, Complex.norm_ofNat, norm_mul, Complex.norm_ofNat] at h
      have h2 : (24 : ℝ) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 24 * Cj * Q := by
        calc (24 : ℝ) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 24 * (Cj * Q) :=
              mul_le_mul_of_nonneg_left hj (by norm_num)
          _ = 24 * Cj * Q := by ring
      have h3 : (314712 : ℝ) ≤ 314712 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ 314712 by norm_num)
        simpa using h
      calc ‖(-314712 : ℂ) - 24 * Work.Kernels.jInvariantFun τ‖
          ≤ 314712 + 24 * ‖Work.Kernels.jInvariantFun τ‖ := h
        _ ≤ 314712 * Q + 24 * Cj * Q := add_le_add h3 h2
        _ = (314712 + 24 * Cj) * Q := by ring
    -- ## Block A
    have hsc : ‖(2 : ℂ) * ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2‖
        ≤ (24 / Real.pi + 8) * T ^ 2 := by
      have e1 : ‖(2 : ℂ) * ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * (z : ℂ)‖
          = 2 * (6 / Real.pi) * ‖(z : ℂ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat, hcn]
      have e2 : ‖(2 : ℂ) * (z : ℂ) ^ 2‖ = 2 * ‖(z : ℂ)‖ ^ 2 := by
        rw [norm_mul, Complex.norm_ofNat, norm_pow]
      calc ‖(2 : ℂ) * ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2‖
          ≤ ‖(2 : ℂ) * ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * (z : ℂ)‖
              + ‖(2 : ℂ) * (z : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = 2 * (6 / Real.pi) * ‖(z : ℂ)‖ + 2 * ‖(z : ℂ)‖ ^ 2 := by rw [e1, e2]
        _ ≤ (24 / Real.pi + 8) * T ^ 2 := by
            have h1 : ‖(z : ℂ)‖ ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzcn 2
            rw [show (2 * T) ^ 2 = 4 * T ^ 2 by ring] at h1
            have h2 : 2 * (6 / Real.pi) * ‖(z : ℂ)‖ ≤ 2 * (6 / Real.pi) * (2 * T) :=
              mul_le_mul_of_nonneg_left hzcn (by positivity)
            rw [show 2 * (6 / Real.pi) * (2 * T) = (24 / Real.pi) * T by ring] at h2
            have h3 : (24 / Real.pi) * T ≤ (24 / Real.pi) * T ^ 2 :=
              mul_le_mul_of_nonneg_left hTleT2 (by positivity)
            have h4 : 2 * ‖(z : ℂ)‖ ^ 2 ≤ 2 * (4 * T ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
            have he : (24 / Real.pi + 8) * T ^ 2
                = (24 / Real.pi) * T ^ 2 + 8 * T ^ 2 := by ring
            rw [he]; linarith [h2, h3, h4]
    have hX : ‖(τ : ℂ) * Work.Kernels.E6Fun τ
            * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)‖
        ≤ C6 * (24 / Real.pi + 8) * (S ^ (2 + N14) * T ^ 2) := by
      rw [norm_mul, norm_mul]
      calc ‖(τ : ℂ)‖ * ‖Work.Kernels.E6Fun τ‖
              * ‖(2 : ℂ) * ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2‖
          ≤ S ^ (2 + N14) * C6 * ((24 / Real.pi + 8) * T ^ 2) :=
            mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hτS hE6 hsc
        _ = C6 * (24 / Real.pi + 8) * (S ^ (2 + N14) * T ^ 2) := by ring
    have hY : ‖(2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2‖
        ≤ 2 * C0 * (3 / 2) * 4 * (S ^ (2 + N14) * T ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
      calc (2 : ℝ) * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖ * ‖(z : ℂ)‖ ^ 2
          ≤ 2 * (C0 * S ^ (2 + N14)) * (3 / 2) * (4 * T ^ 2) :=
            mul4_le (by norm_num) (norm_nonneg _) (norm_nonneg _) (pow_nonneg (norm_nonneg _) 2)
              (le_refl 2) hφ0S hE4 hz4T
        _ = 2 * C0 * (3 / 2) * 4 * (S ^ (2 + N14) * T ^ 2) := by ring
    have hA1 : ‖(-576 : ℂ) * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2‖
        ≤ 576 * C6 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
      calc (576 : ℝ) * ‖(τ : ℂ)‖ * ‖Work.Kernels.E6Fun τ‖ * ‖(z : ℂ)‖ ^ 2
          ≤ 576 * S ^ (2 + N14) * C6 * (4 * T ^ 2 * Q ^ 2) :=
            mul4_le (by norm_num) (norm_nonneg _) (norm_nonneg _) (pow_nonneg (norm_nonneg _) 2)
              (le_refl 576) hτS hE6 hzcq
        _ = 576 * C6 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by ring
    have hA2 : ‖(72 : ℂ) * ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)‖
        ≤ 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      have hsum : ‖(τ : ℂ) * Work.Kernels.E6Fun τ
              * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2‖
          ≤ (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
              * (S ^ (2 + N14) * T ^ 2) := by
        calc ‖(τ : ℂ) * Work.Kernels.E6Fun τ
                * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
              + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2‖
            ≤ ‖(τ : ℂ) * Work.Kernels.E6Fun τ
                * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)‖
              + ‖(2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2‖ :=
                norm_add_le _ _
          _ ≤ C6 * (24 / Real.pi + 8) * (S ^ (2 + N14) * T ^ 2)
                + 2 * C0 * (3 / 2) * 4 * (S ^ (2 + N14) * T ^ 2) := add_le_add hX hY
          _ = (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
                * (S ^ (2 + N14) * T ^ 2) := by ring
      rw [norm_mul, Complex.norm_ofNat]
      calc (72 : ℝ) * ‖(τ : ℂ) * Work.Kernels.E6Fun τ
              * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2‖
          ≤ 72 * ((C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
                * (S ^ (2 + N14) * T ^ 2)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4) * (S ^ (2 + N14) * T ^ 2) := by ring
        _ ≤ 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
            have hST : (0 : ℝ) ≤ S ^ (2 + N14) * T ^ 2 := by positivity
            have hQQ : S ^ (2 + N14) * T ^ 2 ≤ S ^ (2 + N14) * T ^ 2 * Q ^ 2 :=
              prod_le_prod_mul_sq (by positivity) (by positivity) hQ1
            exact mul_le_mul_of_nonneg_left hQQ (by positivity)
    have hA : ‖AA‖ ≤ KAc C0 C6 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [hAA]
      have htri := norm_sub_le ((-576 : ℂ) * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2)
        ((72 : ℂ) * ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (2 * (6 * Complex.I / (Real.pi : ℂ)) * (z : ℂ) - 2 * (z : ℂ) ^ 2)
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2))
      rw [KAc]
      have hdist : (576 * C6 * 4 + 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4))
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
          = 576 * C6 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
            + 72 * (C6 * (24 / Real.pi + 8) + 2 * C0 * (3 / 2) * 4)
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by ring
      rw [hdist]
      linarith [htri, hA1, hA2]
    -- ## Block B
    have hφE : ‖Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
          / Work.Kernels.DeltaFun τ‖ ≤ C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q) := by
      have he : ‖Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
            / Work.Kernels.DeltaFun τ‖
          = ‖Work.Kernels.phi2 τ‖ * ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖
            * ‖(z : ℂ) ^ 2‖ := by
        have hc : Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              / Work.Kernels.DeltaFun τ
            = Work.Kernels.phi2 τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
              * (z : ℂ) ^ 2 := by ring
        rw [hc, norm_mul, norm_mul]
      rw [he]
      have hZ : ‖(z : ℂ) ^ 2‖ ≤ 4 * T ^ 2 := by rw [norm_pow]; exact hz4T
      calc ‖Work.Kernels.phi2 τ‖
              * ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖ * ‖(z : ℂ) ^ 2‖
          ≤ (C2 * S ^ (2 : ℝ)) * (C14 * S ^ N14 * Q) * (4 * T ^ 2) :=
            mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hφ2 hE14 hZ
        _ = C2 * C14 * 4 * (S ^ (2 : ℝ) * S ^ N14) * T ^ 2 * Q := by ring
        _ = C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q) := by
            rw [← Real.rpow_add hSpos]; ring
    have hB1 : ‖(-24 : ℂ) * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
        / Work.Kernels.DeltaFun τ)‖ ≤ 24 * C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc (24 : ℝ) * ‖Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              / Work.Kernels.DeltaFun τ‖
          ≤ 24 * (C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q)) :=
            mul_le_mul_of_nonneg_left hφE (by norm_num)
        _ = 24 * C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q) := by ring
        _ ≤ 24 * C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
            have hQQ : S ^ (2 + N14) * T ^ 2 * Q ≤ S ^ (2 + N14) * T ^ 2 * Q ^ 2 :=
              mul_le_mul_of_nonneg_left hQle (by positivity)
            exact mul_le_mul_of_nonneg_left hQQ (by positivity)
    have hX1 : ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2
            * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
          - 48 * (z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))
            * (Work.Kernels.jInvariantFun τ - 240)‖
        ≤ ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj) + 96 * (2 + 6 / Real.pi) * (Cj + 240))
            * T ^ 2 * Q := by
      have e1 : ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2
            * (-117360 - 24 * Work.Kernels.jInvariantFun τ)‖
          = ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
            * ‖(-117360 - 24 * Work.Kernels.jInvariantFun τ)‖ := by rw [norm_mul]
      have e2 : ‖(48 : ℂ) * (z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))
            * (Work.Kernels.jInvariantFun τ - 240)‖
          = 48 * ‖(z : ℂ)‖ * ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
            * ‖Work.Kernels.jInvariantFun τ - 240‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      calc ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2
              * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
            - 48 * (z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))
              * (Work.Kernels.jInvariantFun τ - 240)‖
          ≤ ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2
              * (-117360 - 24 * Work.Kernels.jInvariantFun τ)‖
            + ‖(48 : ℂ) * (z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))
              * (Work.Kernels.jInvariantFun τ - 240)‖ := norm_sub_le _ _
        _ = ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
              * ‖(-117360 - 24 * Work.Kernels.jInvariantFun τ)‖
            + 48 * ‖(z : ℂ)‖ * ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
              * ‖Work.Kernels.jInvariantFun τ - 240‖ := by rw [e1, e2]
        _ ≤ ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj) + 96 * (2 + 6 / Real.pi) * (Cj + 240))
              * T ^ 2 * Q := by
            have hP1 : ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
                  * ‖(-117360 - 24 * Work.Kernels.jInvariantFun τ)‖
                ≤ ((2 + 6 / Real.pi) ^ 2 * T ^ 2) * ((117360 + 24 * Cj) * Q) :=
              mul_le_mul hzcsub2 hK1 (norm_nonneg _) (by positivity)
            have hP2 : 48 * ‖(z : ℂ)‖ * ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
                  * ‖Work.Kernels.jInvariantFun τ - 240‖
                ≤ 48 * (2 * T) * ((2 + 6 / Real.pi) * T) * ((Cj + 240) * Q) :=
              mul4_le (by norm_num) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
                (le_refl 48) hzcn hzcsub hj240
            calc ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
                    * ‖(-117360 - 24 * Work.Kernels.jInvariantFun τ)‖
                  + 48 * ‖(z : ℂ)‖ * ‖(z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
                    * ‖Work.Kernels.jInvariantFun τ - 240‖
                ≤ ((2 + 6 / Real.pi) ^ 2 * T ^ 2) * ((117360 + 24 * Cj) * Q)
                  + 48 * (2 * T) * ((2 + 6 / Real.pi) * T) * ((Cj + 240) * Q) :=
                    add_le_add hP1 hP2
              _ = ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj)
                    + 96 * (2 + 6 / Real.pi) * (Cj + 240)) * T ^ 2 * Q := by ring
    have hB2 : ‖(τ : ℂ) * Work.Kernels.E6Fun τ
            * (((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                  * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
              - 48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
                  * (Work.Kernels.jInvariantFun τ - 240))‖
        ≤ C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj) + 96 * (2 + 6 / Real.pi) * (Cj + 240))
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [norm_mul, norm_mul]
      calc ‖(τ : ℂ)‖ * ‖Work.Kernels.E6Fun τ‖
              * ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2
                  * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
                - 48 * (z : ℂ) * ((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ))
                  * (Work.Kernels.jInvariantFun τ - 240)‖
          ≤ S ^ (2 + N14) * C6
              * (((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj)
                  + 96 * (2 + 6 / Real.pi) * (Cj + 240)) * T ^ 2 * Q) :=
            mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hτS hE6 hX1
        _ = C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj)
              + 96 * (2 + 6 / Real.pi) * (Cj + 240)) * (S ^ (2 + N14) * T ^ 2 * Q) := by ring
        _ ≤ C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj)
              + 96 * (2 + 6 / Real.pi) * (Cj + 240)) * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
            have hQQ : S ^ (2 + N14) * T ^ 2 * Q ≤ S ^ (2 + N14) * T ^ 2 * Q ^ 2 :=
              mul_le_mul_of_nonneg_left hQle (by positivity)
            exact mul_le_mul_of_nonneg_left hQQ (by positivity)
    have hX2 : ‖((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
            * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
          - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)‖
        ≤ ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984)) * T ^ 2 * Q := by
      have e1 : ‖((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
            * (-314712 - 24 * Work.Kernels.jInvariantFun τ)‖
          = ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
            * ‖(-314712 - 24 * Work.Kernels.jInvariantFun τ)‖ := by rw [norm_mul]
      have e2 : ‖(24 : ℂ) * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)‖
          = 24 * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.jInvariantFun τ - 984‖ := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
      calc ‖((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
              * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
            - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)‖
          ≤ ‖((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
              * (-314712 - 24 * Work.Kernels.jInvariantFun τ)‖
            + ‖(24 : ℂ) * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)‖ := norm_sub_le _ _
        _ = ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
              * ‖(-314712 - 24 * Work.Kernels.jInvariantFun τ)‖
            + 24 * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.jInvariantFun τ - 984‖ := by rw [e1, e2]
        _ ≤ ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984)) * T ^ 2 * Q := by
            have hP1 : ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
                  * ‖(-314712 - 24 * Work.Kernels.jInvariantFun τ)‖
                ≤ ((4 + 12 / Real.pi) * T ^ 2) * ((314712 + 24 * Cj) * Q) :=
              mul_le_mul hzsqcz hK2 (norm_nonneg _) (by positivity)
            have hP2 : 24 * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.jInvariantFun τ - 984‖
                ≤ 24 * (4 * T ^ 2) * ((Cj + 984) * Q) :=
              mul3_le (by norm_num) (pow_nonneg (norm_nonneg _) 2) (norm_nonneg _)
                (le_refl 24) hz4T hj984
            calc ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
                    * ‖(-314712 - 24 * Work.Kernels.jInvariantFun τ)‖
                  + 24 * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.jInvariantFun τ - 984‖
                ≤ ((4 + 12 / Real.pi) * T ^ 2) * ((314712 + 24 * Cj) * Q)
                  + 24 * (4 * T ^ 2) * ((Cj + 984) * Q) := add_le_add hP1 hP2
              _ = ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984)) * T ^ 2 * Q := by ring
    have hB3 : ‖(2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * (((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
                  * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
              - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984))‖
        ≤ 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984))
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      calc (2 : ℝ) * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
              * ‖((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
                  * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
                - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)‖
          ≤ 2 * (C0 * S ^ (2 + N14)) * (3 / 2)
              * (((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984)) * T ^ 2 * Q) :=
            mul4_le (by norm_num) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              (le_refl 2) hφ0S hE4 hX2
        _ = 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984))
              * (S ^ (2 + N14) * T ^ 2 * Q) := by ring
        _ ≤ 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984))
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
            have hQQ : S ^ (2 + N14) * T ^ 2 * Q ≤ S ^ (2 + N14) * T ^ 2 * Q ^ 2 :=
              mul_le_mul_of_nonneg_left hQle (by positivity)
            exact mul_le_mul_of_nonneg_left hQQ (by positivity)
    have hB : ‖BB‖ ≤ KBc C0 C2 C6 C14 Cj * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [hBB]
      have htri1 := norm_add_le
        ((-24 : ℂ) * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
            / Work.Kernels.DeltaFun τ))
        ((τ : ℂ) * Work.Kernels.E6Fun τ
            * (((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                  * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
              - 48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
                  * (Work.Kernels.jInvariantFun τ - 240)))
      have htri2 := norm_sub_le
        (((-24 : ℂ) * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
            / Work.Kernels.DeltaFun τ))
          + ((τ : ℂ) * Work.Kernels.E6Fun τ
            * (((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                  * (-117360 - 24 * Work.Kernels.jInvariantFun τ)
              - 48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
                  * (Work.Kernels.jInvariantFun τ - 240))))
        ((2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * (((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
                  * (-314712 - 24 * Work.Kernels.jInvariantFun τ)
              - 24 * (z : ℂ) ^ 2 * (Work.Kernels.jInvariantFun τ - 984)))
      rw [KBc]
      have hdist : (24 * C2 * C14 * 4
              + C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj) + 96 * (2 + 6 / Real.pi) * (Cj + 240))
              + 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984)))
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
          = 24 * C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
            + C6 * ((2 + 6 / Real.pi) ^ 2 * (117360 + 24 * Cj) + 96 * (2 + 6 / Real.pi) * (Cj + 240))
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
            + 2 * C0 * (3 / 2) * ((4 + 12 / Real.pi) * (314712 + 24 * Cj) + 96 * (Cj + 984))
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by ring
      rw [hdist]
      linarith [htri1, htri2, hB1, hB2, hB3]
    -- ## Block C
    have hW2 : ‖(τ : ℂ) * Work.Kernels.E6Fun τ
            * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
            * (Work.Kernels.jInvariantFun τ - 240)‖
        ≤ C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240) * (S ^ (2 + N14) * T ^ 2 * Q) := by
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖(τ : ℂ)‖ * ‖Work.Kernels.E6Fun τ‖
              * ‖((z : ℂ) - (6 : ℂ) * Complex.I / (Real.pi : ℂ)) ^ 2‖
              * ‖Work.Kernels.jInvariantFun τ - 240‖
          ≤ S ^ (2 + N14) * C6 * ((2 + 6 / Real.pi) ^ 2 * T ^ 2) * ((Cj + 240) * Q) :=
            mul4_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              hτS hE6 hzcsub2 hj240
        _ = C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240) * (S ^ (2 + N14) * T ^ 2 * Q) := by ring
    have hW3 : ‖(2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * ((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
            * (Work.Kernels.jInvariantFun τ - 984)‖
        ≤ 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984) * (S ^ (2 + N14) * T ^ 2 * Q) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      calc (2 : ℝ) * ‖Work.Kernels.phi0 τ‖ * ‖Work.Kernels.E4Fun τ‖
              * ‖(z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ)‖
              * ‖Work.Kernels.jInvariantFun τ - 984‖
          ≤ 2 * (C0 * S ^ (2 + N14)) * (3 / 2) * ((4 + 12 / Real.pi) * T ^ 2)
              * ((Cj + 984) * Q) :=
            mul5_le (by norm_num) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              (le_refl 2) hφ0S hE4 hzsqcz hj984
        _ = 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984)
              * (S ^ (2 + N14) * T ^ 2 * Q) := by ring
    have hW : ‖Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 / Work.Kernels.DeltaFun τ
            + (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                * (Work.Kernels.jInvariantFun τ - 240)
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                * ((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
                * (Work.Kernels.jInvariantFun τ - 984)‖
        ≤ (C2 * C14 * 4 + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240)
            + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984))
            * (S ^ (2 + N14) * T ^ 2 * Q) := by
      have ht1 := norm_add_le
        (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 / Work.Kernels.DeltaFun τ)
        ((τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
            * (Work.Kernels.jInvariantFun τ - 240))
      have ht2 := norm_sub_le
        ((Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 / Work.Kernels.DeltaFun τ)
          + ((τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
              * (Work.Kernels.jInvariantFun τ - 240)))
        ((2 : ℂ) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * ((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
            * (Work.Kernels.jInvariantFun τ - 984))
      rw [show (C2 * C14 * 4 + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240)
              + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984)) * (S ^ (2 + N14) * T ^ 2 * Q)
          = C2 * C14 * 4 * (S ^ (2 + N14) * T ^ 2 * Q)
            + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240) * (S ^ (2 + N14) * T ^ 2 * Q)
            + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984)
              * (S ^ (2 + N14) * T ^ 2 * Q) by ring]
      linarith [ht1, ht2, hφE, hW2, hW3]
    have hC : ‖CC‖ ≤ KCc C0 C2 C6 C14 Cj * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      rw [hCC, norm_mul]
      rw [KCc]
      calc ‖Work.Kernels.jInvariantFun τ - 720‖
              * ‖Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 / Work.Kernels.DeltaFun τ
                + (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
                    * (Work.Kernels.jInvariantFun τ - 240)
                - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                    * ((z : ℂ) ^ 2 - (6 : ℂ) * Complex.I / (Real.pi : ℂ) * (z : ℂ))
                    * (Work.Kernels.jInvariantFun τ - 984)‖
          ≤ ((Cj + 720) * Q) * ((C2 * C14 * 4 + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240)
              + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984))
              * (S ^ (2 + N14) * T ^ 2 * Q)) :=
            mul_le_mul hj720 hW (norm_nonneg _) (by positivity)
        _ = (Cj + 720) * (C2 * C14 * 4 + C6 * (2 + 6 / Real.pi) ^ 2 * (Cj + 240)
              + 2 * C0 * (3 / 2) * (4 + 12 / Real.pi) * (Cj + 984))
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by ring
    -- ## Assembly
    have hX : ‖AA - BB - CC‖ ≤ (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj)
        * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) := by
      have h1 := norm_sub_le AA BB
      have h2 := norm_sub_le (AA - BB) CC
      rw [show (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj)
            * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
          = KAc C0 C6 * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
            + KBc C0 C2 C6 C14 Cj * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)
            + KCc C0 C2 C6 C14 Cj * (S ^ (2 + N14) * T ^ 2 * Q ^ 2) by ring]
      linarith [h1, h2, hA, hB, hC]
    rw [norm_mul]
    calc ‖Work.Asymptotics.Compact.tailC⁻¹‖ * ‖AA - BB - CC‖
        ≤ ‖Work.Asymptotics.Compact.tailC⁻¹‖
            * ((KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj)
              * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)) :=
          mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ ≤ (‖Work.Asymptotics.Compact.tailC⁻¹‖
              * (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj) + 1)
            * Q ^ 2 * S ^ (2 + N14) * T ^ 2 := by
          have he : (‖Work.Asymptotics.Compact.tailC⁻¹‖
                * (KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj) + 1)
                * Q ^ 2 * S ^ (2 + N14) * T ^ 2
              = ‖Work.Asymptotics.Compact.tailC⁻¹‖
                  * ((KAc C0 C6 + KBc C0 C2 C6 C14 Cj + KCc C0 C2 C6 C14 Cj)
                    * (S ^ (2 + N14) * T ^ 2 * Q ^ 2)) + Q ^ 2 * S ^ (2 + N14) * T ^ 2 := by ring
          rw [he]
          have h0 : (0 : ℝ) ≤ Q ^ 2 * S ^ (2 + N14) * T ^ 2 := by positivity
          linarith

end

end Work.Asymptotics.KhatE1
