import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

set_option maxHeartbeats 800000
set_option linter.all false

/-- Auxiliary: `1 + K₀ + K₄ + K₁` is bounded by the product of the three prices. -/
lemma nsumG3Dz_one_add {α M Ce k0 k4 k1 K0 K4 K1 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk1 : 0 ≤ k1)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    1 + K0 + K4 + K1 ≤ (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hAm1 : 1 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hαhalf : 1 ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(1 / 2 : ℝ)) ≤ (0 : ℝ) by norm_num)
    simpa using h
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hW1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hαhalf hAm1) hm1
  have hK0W : K0 ≤ k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    rw [show k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)
        = k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) from by ring] at hp0
    exact hp0
  have hK4W : K4 ≤ k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have hMM : M ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      calc M ≤ 1 + M := by linarith
        _ ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := le_mul_of_one_le_left hm0 hαhalf
    have h1 : k4 * (1 + |Ce|) * M ≤ k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
      mul_le_mul_of_nonneg_left hMM (mul_nonneg hk4 hAm0)
    have h2 : k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M))
        = k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [hp4, h1, h2]
  have hK1W : K1 ≤ k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have hk1' : k1 ≤ k1 * α ^ (-(1 / 2 : ℝ)) := le_mul_of_one_le_right hk1 hαhalf
    have h1 : k1 * (1 + |Ce|) ≤ (k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|) :=
      mul_le_mul_of_nonneg_right hk1' hAm0
    have h2 : k1 * (1 + |Ce|) * (1 + M) ≤ ((k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)) * (1 + M) :=
      mul_le_mul_of_nonneg_right h1 hm0
    have h3 : ((k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)) * (1 + M)
        = k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [hp1, h2, h3]
  have h1 : 1 + K0 + K4 + K1 ≤ 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    linarith [hW1, hK0W, hK4W, hK1W]
  have h2 : 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      = (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
  linarith [h1, h2]

/-- Auxiliary: `K₄ + K₆` is bounded by the product of the two prices. -/
lemma nsumG3Dz_K46 {M Ce H k4 k6 K4 K6 : ℝ} (hM : 0 ≤ M) (hH0 : 0 ≤ H)
    (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6)
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    K4 + K6 ≤ (k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H) := by
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hh0 : 0 ≤ 1 + H := by linarith
  have hh1 : 1 ≤ 1 + H := by linarith
  have hB4 : K4 ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have s1 : k4 * (1 + |Ce|) * M ≤ k4 * (1 + |Ce|) * (1 + M) :=
      mul_le_mul_of_nonneg_left (by linarith : M ≤ 1 + M) (mul_nonneg hk4 hAm0)
    have s2 : k4 * (1 + |Ce|) * (1 + M) ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg hk4 hAm0) hm0) hh1
    linarith [hp4, s1, s2]
  have hB6 : K6 ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have s1 : k6 * (1 + |Ce|) * H ≤ k6 * (1 + |Ce|) * (1 + M) * H :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hk6 hAm0) hm1) hH0
    have s2 : k6 * (1 + |Ce|) * (1 + M) * H ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      mul_le_mul_of_nonneg_left (by linarith : H ≤ 1 + H) (mul_nonneg (mul_nonneg hk6 hAm0) hm0)
    linarith [hp6, s1, s2]
  nlinarith [hB4, hB6]

/-- First half of the arithmetic: the `(1 + K₀ + K₄ + K₁)` bracket. -/
lemma nsumG3Dz_first {α M Ce Cs S C0 k0 k4 k6 k1 K0 K4 K1 : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hS0 : 0 ≤ S)
    (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) := by
  have hA : 1 + K0 + K4 + K1
      ≤ (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) :=
    nsumG3Dz_one_add hα0 hα1 hM hk0 hk4 hk1 hp0 hp4 hp1
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hs0 : 0 ≤ 1 + S := by linarith
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm24 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm2nn : 0 ≤ (1 + M) ^ 2 := pow_nonneg hm0 2
  have hm4nn : 0 ≤ (1 + M) ^ 4 := pow_nonneg hm0 4
  have hABnn : 0 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB1 : 1 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB4nn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := pow_nonneg hABnn 4
  have hAm_le : 1 + |Ce| ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h3 : 1 + |Ce| + |Cs| ≤ (1 + |Ce| + |Cs|) ^ 4 := le_self_pow₀ hAB1 (by norm_num)
    linarith [abs_nonneg Cs]
  have hα4nn : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10nn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαhalf0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαcomb : α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα0]
    rw [show -(4 : ℝ) + -(1 / 2 : ℝ) = -(9 / 2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαcomb0 : 0 ≤ α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hα4nn hαhalf0
  have hC0α4 : 0 ≤ C0 * α ^ (-(4 : ℝ)) := mul_nonneg hC0 hα4nn
  have hT0 : 0 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT'T : 1 + k0 + k4 + k1 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT1b : (1 + K0 + K4 + K1) * (1 + M) * (1 + S)
      ≤ ((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
          * (1 + M) * (1 + S) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hm0) hs0
  have hT1c : C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ C0 * α ^ (-(4 : ℝ))
          * (((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
              * (1 + M) * (1 + S)) :=
    mul_le_mul_of_nonneg_left hT1b hC0α4
  have hT1d : C0 * α ^ (-(4 : ℝ))
          * (((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
              * (1 + M) * (1 + S))
      = (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
          * (1 + |Ce|) * (1 + M) ^ 2 * (1 + S) := by ring
  have e1 : (1 + k0 + k4 + k1) * C0 ≤ (1 + k0 + k4 + k6 + k1) * C0 :=
    mul_le_mul_of_nonneg_right hT'T hC0
  have e2 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) :=
    mul_le_mul e1 hαcomb hαcomb0 (mul_nonneg hT0 hC0)
  have e3 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 :=
    mul_le_mul e2 hAm_le hAm0 (mul_nonneg (mul_nonneg hT0 hC0) hα10nn)
  have e4 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
          * (1 + M) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 :=
    mul_le_mul e3 hm24 hm2nn (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn)
  have hT1e : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
          * (1 + M) ^ 2 * (1 + S)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    mul_le_mul e4 (le_refl (1 + S)) hs0
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  exact le_trans hT1c (le_trans (le_of_eq hT1d) hT1e)

/-- Second half of the arithmetic: the `(K₄ + K₆)` bracket. -/
lemma nsumG3Dz_second {α M Ce Cs S H C0 k0 k4 k6 k1 K4 K6 : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hSH : S = H ^ 2) (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
  have hB : K4 + K6 ≤ (k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H) :=
    nsumG3Dz_K46 hM hH0 hk4 hk6 hp4 hp6
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hh0 : 0 ≤ 1 + H := by linarith
  have hs0 : 0 ≤ 1 + S := by linarith
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm24 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm2nn : 0 ≤ (1 + M) ^ 2 := pow_nonneg hm0 2
  have hm4nn : 0 ≤ (1 + M) ^ 4 := pow_nonneg hm0 4
  have hH2nn : 0 ≤ (1 + H) ^ 2 := pow_nonneg hh0 2
  have hH2S : (1 + H) ^ 2 ≤ 4 * (1 + S) := by nlinarith [hSH, sq_nonneg (H - 1 / 3)]
  have hABnn : 0 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB1 : 1 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB4nn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := pow_nonneg hABnn 4
  have hAm_le : 1 + |Ce| ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h3 : 1 + |Ce| + |Cs| ≤ (1 + |Ce| + |Cs|) ^ 4 := le_self_pow₀ hAB1 (by norm_num)
    linarith [abs_nonneg Cs]
  have hα4nn : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10nn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα4_le_10 : α ^ (-(4 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hC0α4 : 0 ≤ C0 * α ^ (-(4 : ℝ)) := mul_nonneg hC0 hα4nn
  have hT0 : 0 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT2b : (K4 + K6) * (1 + M) * (1 + H)
      ≤ ((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hm0) hh0
  have hT2c : C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ C0 * α ^ (-(4 : ℝ))
          * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H)) :=
    mul_le_mul_of_nonneg_left hT2b hC0α4
  have hT2d : C0 * α ^ (-(4 : ℝ))
          * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H))
      = (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2 := by ring
  have e1 : k4 + k6 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have e2 : (k4 + k6) * C0 ≤ (1 + k0 + k4 + k6 + k1) * C0 :=
    mul_le_mul_of_nonneg_right e1 hC0
  have e3 : (k4 + k6) * C0 * α ^ (-(4 : ℝ))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) :=
    mul_le_mul e2 hα4_le_10 hα4nn (mul_nonneg hT0 hC0)
  have e4 : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 :=
    mul_le_mul e3 hAm_le hAm0 (mul_nonneg (mul_nonneg hT0 hC0) hα10nn)
  have e5 : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 :=
    mul_le_mul e4 hm24 hm2nn (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn)
  have hT2e : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + H) ^ 2 :=
    mul_le_mul e5 (le_refl ((1 + H) ^ 2)) hH2nn
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  have hT2f : (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (4 * (1 + S)) :=
    mul_le_mul_of_nonneg_left hH2S
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  have hT2g : (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (4 * (1 + S))
      = 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by ring
  exact le_trans hT2c (le_trans (le_of_eq hT2d) (le_trans hT2e (le_trans hT2f (le_of_eq hT2g))))

theorem arithNsumG3Dz {X α M Ce Cs S H C0 k0 k4 k6 k1 K0 K4 K6 K1 : ℝ}
    (hX : X ≤ C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S)
      + (K4 + K6) * (1 + M) * (1 + H)))
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0)
    (hSH : S = H ^ 2) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hK1 : 0 ≤ K1) (hM : 0 ≤ M)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    X ≤ (16 * (1 + k0 + k4 + k6 + k1) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
  have hfin1 : C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    nsumG3Dz_first (Cs := Cs) hα0 hα1 hC0 hM hS0 hk0 hk4 hk6 hk1 hp0 hp4 hp1
  have hfin2 : C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) :=
    nsumG3Dz_second (Cs := Cs) (S := S) hα0 hα1 hC0 hM hH0 hS0 hSH hk0 hk4 hk6 hk1 hp4 hp6
  have hsplit : C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      = C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
        + C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H)) := by ring
  have hsum : C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      ≤ 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
    rw [hsplit]
    linarith [hfin1, hfin2]
  have h16 : 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S))
      ≤ 16 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
    have hnn : 0 ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
        * (1 + M) ^ 4 * (1 + S) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (by linarith) hC0) (Real.rpow_nonneg hα0.le _))
          (pow_nonneg (by linarith [abs_nonneg Ce, abs_nonneg Cs]) 4))
            (pow_nonneg (by linarith) 4)) (by linarith)
    linarith
  calc X ≤ C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H)) := hX
    _ ≤ 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := hsum
    _ ≤ 16 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := h16
    _ = (16 * (1 + k0 + k4 + k6 + k1) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
