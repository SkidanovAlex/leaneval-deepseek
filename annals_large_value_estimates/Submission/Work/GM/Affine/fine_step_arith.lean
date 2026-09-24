import Mathlib

namespace Work.GM.Affine

theorem fine_step_arith {C₁ C₂ T δs η M U V J Jb : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hT : 1 ≤ T) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hδs : 0 ≤ δs) (hη : 0 ≤ η) (hJ : 0 ≤ J) (hJb : 0 ≤ Jb)
    (h : J ≤ C₁ * T ^ δs * (M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb))
    (hJble : Jb ≤ C₂ * T ^ η * (M ^ 6 * U ^ 2 + M ^ 4 * V)) :
    J ≤ C₁ * (1 + 3 * Real.sqrt C₂ / 2) * T ^ (δs + η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : (0 : ℝ) ≤ T := le_of_lt hTpos
  have hη2 : 0 ≤ η / 2 := by linarith
  have hA : 0 ≤ M ^ 6 * U ^ 2 := mul_nonneg (pow_nonneg hM 6) (pow_nonneg hU 2)
  have hB : 0 ≤ M ^ 4 * V := mul_nonneg (pow_nonneg hM 4) hV
  have hAB : 0 ≤ M ^ 6 * U ^ 2 + M ^ 4 * V := add_nonneg hA hB
  have hsAB : 0 ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := Real.sqrt_nonneg _
  have hsC2 : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
  have hTηnn : 0 ≤ T ^ (η / 2) := Real.rpow_nonneg hTnn _
  have hTη1 : 1 ≤ T ^ (η / 2) := Real.one_le_rpow hT hη2
  -- key comparison M^2 * sqrt V ≤ sqrt (M^6 U^2 + M^4 V)
  have hMV : M ^ 2 * Real.sqrt V ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have heq : M ^ 2 * Real.sqrt V = Real.sqrt (M ^ 4 * V) := by
      rw [Real.sqrt_mul (pow_nonneg hM 4) V]
      rw [show Real.sqrt (M ^ 4) = M ^ 2 by
        rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (pow_nonneg hM 2)]]
    rw [heq]
    exact Real.sqrt_le_sqrt (by linarith [hA])
  -- sqrt T^η = T^(η/2)
  have hsqT : Real.sqrt (T ^ η) = T ^ (η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTnn η (1 / 2)]
    congr 1
    ring
  have hsqrtJb :
      Real.sqrt Jb ≤ Real.sqrt C₂ * T ^ (η / 2) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hs := Real.sqrt_le_sqrt hJble
    have harg : C₂ * T ^ η * (M ^ 6 * U ^ 2 + M ^ 4 * V)
        = (C₂ * T ^ η) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by ring
    rw [harg] at hs
    rw [Real.sqrt_mul (mul_nonneg hC₂ (Real.rpow_nonneg hTnn η))
          (M ^ 6 * U ^ 2 + M ^ 4 * V)] at hs
    have hsq : Real.sqrt (C₂ * T ^ η) = Real.sqrt C₂ * T ^ (η / 2) := by
      rw [Real.sqrt_mul hC₂ (T ^ η), hsqT]
    rw [hsq] at hs
    exact hs
  have hstep :
      M ^ 2 * Real.sqrt V * Real.sqrt Jb
        ≤ Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hMVnonneg : 0 ≤ M ^ 2 * Real.sqrt V :=
      mul_nonneg (pow_nonneg hM 2) (Real.sqrt_nonneg V)
    have hmid :
        M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)
          ≤ M ^ 6 * U ^ 2 + M ^ 4 * V := by
      calc M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)
          ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
            mul_le_mul_of_nonneg_right hMV hsAB
        _ = M ^ 6 * U ^ 2 + M ^ 4 * V := by rw [← pow_two, Real.sq_sqrt hAB]
    calc M ^ 2 * Real.sqrt V * Real.sqrt Jb
        ≤ M ^ 2 * Real.sqrt V *
            (Real.sqrt C₂ * T ^ (η / 2) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)) :=
          mul_le_mul_of_nonneg_left hsqrtJb hMVnonneg
      _ = (Real.sqrt C₂ * T ^ (η / 2)) *
            (M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)) := by ring
      _ ≤ (Real.sqrt C₂ * T ^ (η / 2)) * (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
          mul_le_mul_of_nonneg_left hmid (mul_nonneg hsC2 hTηnn)
      _ = Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by ring
  have hmain :
      M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb
        ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hAle : M ^ 6 * U ^ 2 ≤ M ^ 6 * U ^ 2 + M ^ 4 * V := by linarith [hB]
    have hcoef : 1 + Real.sqrt C₂ * T ^ (η / 2)
        ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) := by
      have h1 : 1 + Real.sqrt C₂ * T ^ (η / 2) ≤ (1 + Real.sqrt C₂) * T ^ (η / 2) := by
        nlinarith [hTη1]
      have h2 : (1 + Real.sqrt C₂) * T ^ (η / 2)
          ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) := by
        apply mul_le_mul_of_nonneg_right _ hTηnn
        linarith [hsC2]
      linarith [h1, h2]
    calc M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb
        ≤ (M ^ 6 * U ^ 2 + M ^ 4 * V)
            + Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
          add_le_add hAle hstep
      _ = (1 + Real.sqrt C₂ * T ^ (η / 2)) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by ring
      _ ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
          mul_le_mul_of_nonneg_right hcoef hAB
  calc J ≤ C₁ * T ^ δs * (M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb) := h
    _ ≤ C₁ * T ^ δs *
          ((1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V)) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg hC₁ (Real.rpow_nonneg hTnn δs))
    _ = C₁ * (1 + 3 * Real.sqrt C₂ / 2) * T ^ (δs + η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
        rw [Real.rpow_add hTpos]
        ring

end Work.GM.Affine
