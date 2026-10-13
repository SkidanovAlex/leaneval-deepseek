import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

set_option maxHeartbeats 1000000 in
/-- Monotonicity of a product of four nonnegative terms (left-associated). -/
lemma arithNsumG3Mul_mul_four {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂)
    (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁) (hc0 : 0 ≤ c₁) (hd0 : 0 ≤ d₁)
    (ha2 : 0 ≤ a₂) (hb2 : 0 ≤ b₂) (hc2 : 0 ≤ c₂) (hd2 : 0 ≤ d₂) :
    a₁ * b₁ * c₁ * d₁ ≤ a₂ * b₂ * c₂ * d₂ :=
  mul_le_mul (mul_le_mul (mul_le_mul ha hb hb0 ha2) hc hc0 (mul_nonneg ha2 hb2)) hd hd0
    (mul_nonneg (mul_nonneg ha2 hb2) hc2)

set_option maxHeartbeats 1000000 in
/-- Monotonicity of a product of six nonnegative terms (left-associated). -/
lemma arithNsumG3Mul_mul_six {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : ℝ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) (he : e₁ ≤ e₂) (hf : f₁ ≤ f₂)
    (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁) (hc0 : 0 ≤ c₁) (hd0 : 0 ≤ d₁) (he0 : 0 ≤ e₁) (hf0 : 0 ≤ f₁)
    (ha2 : 0 ≤ a₂) (hb2 : 0 ≤ b₂) (hc2 : 0 ≤ c₂) (hd2 : 0 ≤ d₂) (he2 : 0 ≤ e₂) (hf2 : 0 ≤ f₂) :
    a₁ * b₁ * c₁ * d₁ * e₁ * f₁ ≤ a₂ * b₂ * c₂ * d₂ * e₂ * f₂ := by
  have h1 : a₁ * b₁ ≤ a₂ * b₂ := mul_le_mul ha hb hb0 ha2
  have h2 : a₁ * b₁ * c₁ ≤ a₂ * b₂ * c₂ := mul_le_mul h1 hc hc0 (mul_nonneg ha2 hb2)
  have h3 : a₁ * b₁ * c₁ * d₁ ≤ a₂ * b₂ * c₂ * d₂ :=
    mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha2 hb2) hc2)
  have h4 : a₁ * b₁ * c₁ * d₁ * e₁ ≤ a₂ * b₂ * c₂ * d₂ * e₂ :=
    mul_le_mul h3 he he0 (mul_nonneg (mul_nonneg (mul_nonneg ha2 hb2) hc2) hd2)
  exact mul_le_mul h4 hf hf0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha2 hb2) hc2) hd2) he2)

set_option maxHeartbeats 3200000 in
theorem arithNsumG3Mul {X α M Ce Cs S H C0 k0 k4 k6 K0 K4 K6 : ℝ}
    (hX : X ≤ C0 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H)))
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0)
    (hSH : S = H ^ 2) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hM : 0 ≤ M)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    X ≤ (16 * (1 + k0 + k4 + k6) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hAm1 : 1 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hAB1 : 1 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB4nn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hAm_le : 1 + |Ce| ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h2 : 1 + |Ce| ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Cs]
    have h3 : 1 + |Ce| + |Cs| ≤ (1 + |Ce| + |Cs|) ^ 4 := le_self_pow₀ hAB1 (by norm_num)
    linarith
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hm14 : 1 + M ≤ (1 + M) ^ 4 := le_self_pow₀ hm1 (by norm_num)
  have hm24 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hs0 : 0 ≤ 1 + S := by linarith
  have hh0 : 0 ≤ 1 + H := by linarith
  have hh1 : 1 ≤ 1 + H := by linarith
  have hαhalf : 1 ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(1 / 2 : ℝ)) ≤ (0 : ℝ) by norm_num)
    simpa using h
  have hαhalf0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := by positivity
  have hα3nn : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10nn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα3_le_10 : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαcomb : α ^ (-(3 : ℝ)) * α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα0]
    rw [show -(3 : ℝ) + -(1 / 2 : ℝ) = -(7 / 2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαcomb0 : 0 ≤ α ^ (-(3 : ℝ)) * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hα3nn hαhalf0
  have hC0α3 : 0 ≤ C0 * α ^ (-(3 : ℝ)) := mul_nonneg hC0 hα3nn
  have hT'0 : 0 ≤ 1 + k0 + k4 := by linarith
  have hT0 : 0 ≤ 1 + k0 + k4 + k6 := by linarith
  have hT'T : 1 + k0 + k4 ≤ 1 + k0 + k4 + k6 := by linarith
  have hk46 : k4 + k6 ≤ 1 + k0 + k4 + k6 := by linarith
  -- ### hA : 1 + K0 + K4 ≤ (1+k0+k4) * (α^{-1/2}(1+|Ce|)(1+M))
  have hW1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hαhalf hAm1) hm1
  have hK0W : K0 ≤ k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    rw [show k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)
        = k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) from by ring] at hp0
    exact hp0
  have hK4W : K4 ≤ k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have hMM : M ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      calc M ≤ 1 + M := by linarith
        _ ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := le_mul_of_one_le_left (by linarith) hαhalf
    have h1 : k4 * (1 + |Ce|) * M ≤ k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
      mul_le_mul_of_nonneg_left hMM (by positivity)
    have h2 : k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M))
        = k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [hp4, h1, h2]
  have hA : 1 + K0 + K4 ≤ (1 + k0 + k4) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have h1 : 1 + K0 + K4 ≤ 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
        + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
        + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
      linarith [hW1, hK0W, hK4W]
    have h2 : 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
        + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
        + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
        = (1 + k0 + k4) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [h1, h2]
  -- ### hB : K4 + K6 ≤ (k4+k6)(1+|Ce|)(1+M)(1+H)
  have hB4 : K4 ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have h4 : k4 * (1 + |Ce|) * M * 1 ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      arithNsumG3Mul_mul_four (le_refl k4) (le_refl (1 + |Ce|)) (by linarith : M ≤ 1 + M) hh1
        hk4 hAm0 hM (by norm_num) hk4 hAm0 (by linarith) (by linarith)
    have h5 : k4 * (1 + |Ce|) * M = k4 * (1 + |Ce|) * M * 1 := by ring
    linarith [hp4, h4, h5]
  have hB6 : K6 ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have h5 : k6 * (1 + |Ce|) * H ≤ k6 * (1 + |Ce|) * (1 + M) * H :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hm1) hH0
    have h4 : k6 * (1 + |Ce|) * (1 + M) * H ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      arithNsumG3Mul_mul_four (le_refl k6) (le_refl (1 + |Ce|)) (le_refl (1 + M))
        (by linarith : H ≤ 1 + H) hk6 hAm0 hm0 hH0 hk6 hAm0 hm0 hh0
    linarith [hp6, h5, h4]
  have hB : K4 + K6 ≤ (k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H) := by nlinarith [hB4, hB6]
  -- ### the `H`/`S` inequality
  have hH2S : (1 + H) ^ 2 ≤ 4 * (1 + S) := by nlinarith [hSH, sq_nonneg (H - 1 / 3)]
  -- ### first bracket
  have hT1b : (1 + K0 + K4) * (1 + S)
      ≤ ((1 + k0 + k4) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))) * (1 + S) :=
    mul_le_mul_of_nonneg_right hA hs0
  have hT1c : C0 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + S))
      ≤ C0 * α ^ (-(3 : ℝ))
        * (((1 + k0 + k4) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))) * (1 + S)) :=
    mul_le_mul_of_nonneg_left hT1b hC0α3
  have hT1d : C0 * α ^ (-(3 : ℝ))
        * (((1 + k0 + k4) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))) * (1 + S))
      = (1 + k0 + k4) * C0 * (α ^ (-(3 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
          * (1 + |Ce|) * (1 + M) * (1 + S) := by ring
  have hT1e : (1 + k0 + k4) * C0 * (α ^ (-(3 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
        * (1 + |Ce|) * (1 + M) * (1 + S)
      ≤ (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    arithNsumG3Mul_mul_six hT'T (le_refl C0) hαcomb hAm_le hm14 (le_refl (1 + S))
      hT'0 hC0 hαcomb0 hAm0 hm0 hs0 hT0 hC0 hα10nn hAB4nn hm4nn hs0
  have hfin1 : C0 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + S))
      ≤ (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    le_trans hT1c (le_trans (le_of_eq hT1d) hT1e)
  -- ### second bracket
  have hT2b : (K4 + K6) * (1 + M) * (1 + H)
      ≤ ((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hm0) hh0
  have hT2c : C0 * α ^ (-(3 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ C0 * α ^ (-(3 : ℝ))
        * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H)) :=
    mul_le_mul_of_nonneg_left hT2b hC0α3
  have hT2d : C0 * α ^ (-(3 : ℝ))
        * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H))
      = (k4 + k6) * C0 * α ^ (-(3 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2 := by ring
  have hT2e : (k4 + k6) * C0 * α ^ (-(3 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + H) ^ 2 :=
    arithNsumG3Mul_mul_six hk46 (le_refl C0) hα3_le_10 hAm_le hm24 (le_refl _)
      (by linarith) hC0 hα3nn hAm0 (by positivity) (by positivity)
      hT0 hC0 hα10nn hAB4nn hm4nn (by positivity)
  have hT2f : (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
        * (1 + M) ^ 4 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
        * (1 + M) ^ 4 * (4 * (1 + S)) :=
    mul_le_mul_of_nonneg_left hH2S (by positivity)
  have hT2g : (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
        * (1 + M) ^ 4 * (4 * (1 + S))
      = 4 * ((1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by ring
  have hfin2 : C0 * α ^ (-(3 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ 4 * ((1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) :=
    le_trans hT2c (le_trans (le_of_eq hT2d) (le_trans hT2e (le_trans hT2f (le_of_eq hT2g))))
  -- ### assembly
  have hsplit : C0 * α ^ (-(3 : ℝ))
        * ((1 + K0 + K4) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      = C0 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + S))
        + C0 * α ^ (-(3 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H)) := by ring
  have hsum : C0 * α ^ (-(3 : ℝ))
        * ((1 + K0 + K4) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      ≤ 5 * ((1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
    rw [hsplit]
    linarith [hfin1, hfin2]
  have hnn : 0 ≤ (1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
      * (1 + M) ^ 4 * (1 + S) := by positivity
  calc X ≤ C0 * α ^ (-(3 : ℝ))
        * ((1 + K0 + K4) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H)) := hX
    _ ≤ 5 * ((1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := hsum
    _ ≤ 16 * ((1 + k0 + k4 + k6) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by linarith
    _ = (16 * (1 + k0 + k4 + k6) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
