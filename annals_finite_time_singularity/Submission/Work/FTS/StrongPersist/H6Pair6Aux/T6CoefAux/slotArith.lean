import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

theorem slotArith {α Cpw K0 K4 HkSq : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hCpw : 0 < Cpw)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hH : 0 ≤ HkSq) :
    Real.sqrt (K4 ^ 2 + 1)
        * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
  -- abbreviations: s := α⁻¹ ≥ 1, B := √(10 Cpw + 1), C := 1 + HkSq
  have hs1 : 1 ≤ α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    exact (one_le_inv₀ hα0).2 hα1
  have hs0 : 0 ≤ α ^ (-(1 : ℝ)) := le_trans zero_le_one hs1
  -- α^{-3} = (α^{-1})³
  have hα3 : α ^ (-(3 : ℝ)) = (α ^ (-(1 : ℝ))) ^ 3 := by
    rw [show (-(3 : ℝ)) = (-(1 : ℝ)) + (-(1 : ℝ)) + (-(1 : ℝ)) by norm_num,
      Real.rpow_add hα0, Real.rpow_add hα0]
    ring
  rw [hα3]
  -- √(K4²+1) ≤ 1 + K4
  have hA : Real.sqrt (K4 ^ 2 + 1) ≤ 1 + K4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [hK4]⟩
  -- 10 Cpw s HkSq² + 1 ≤ (10 Cpw s + 1)(1 + HkSq)²
  have hXbound : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
      ≤ (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2 := by
    have key : (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2
        - (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
        = 10 * Cpw * α ^ (-(1 : ℝ)) * (2 * HkSq + 1) + (2 * HkSq + HkSq * HkSq) := by ring
    have h1 : 0 ≤ 10 * Cpw * α ^ (-(1 : ℝ)) * (2 * HkSq + 1) := by positivity
    have h2 : 0 ≤ 2 * HkSq + HkSq * HkSq := by nlinarith
    linarith
  -- √(10 Cpw s + 1) ≤ √(10 Cpw + 1) · s
  have hsq : Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
    have h2 : α ^ (-(1 : ℝ)) ≤ (α ^ (-(1 : ℝ))) ^ 2 := by nlinarith [hs1]
    have hp : 10 * Cpw * α ^ (-(1 : ℝ)) + 1 ≤ (10 * Cpw + 1) * (α ^ (-(1 : ℝ))) ^ 2 := by
      have h1 : 10 * Cpw * α ^ (-(1 : ℝ)) + 1 ≤ (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
        nlinarith [hs1]
      nlinarith [h1, h2, hCpw]
    calc Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1)
        ≤ Real.sqrt ((10 * Cpw + 1) * (α ^ (-(1 : ℝ))) ^ 2) := Real.sqrt_le_sqrt hp
      _ = Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs0]
  -- √(Cpw · 10 · s · HkSq² + 1) ≤ √(10 Cpw + 1) · (1 + HkSq) · s
  have hB : Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by
    calc Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
        ≤ Real.sqrt ((10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2) :=
          Real.sqrt_le_sqrt hXbound
      _ = Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
      _ ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) * (1 + HkSq) :=
          mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by ring
  -- the remaining purely algebraic step, with the three monotonicities
  -- 1 + K4 ≤ 1 + K0 + K4,  √(10Cpw+1) ≤ √(10Cpw+1) + 1,  s ≤ s³
  have hfinal : (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
        * ((1 + K0 + K4) * (1 + HkSq)) := by
    have hs3 : α ^ (-(1 : ℝ)) ≤ (α ^ (-(1 : ℝ))) ^ 3 := by
      simpa using pow_le_pow_right₀ hs1 (show (1 : ℕ) ≤ 3 by norm_num)
    have hDnn : 0 ≤ 1 + K0 + K4 := by linarith
    have hBle : Real.sqrt (10 * Cpw + 1) ≤ Real.sqrt (10 * Cpw + 1) + 1 := by linarith
    have hK : 1 + K4 ≤ 1 + K0 + K4 := by linarith
    have hCnn : 0 ≤ 1 + HkSq := by linarith
    have hprod : 0 ≤ Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by positivity
    have hA' : (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) :=
      mul_le_mul_of_nonneg_right hK hprod
    have hBC : Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))
        ≤ (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ))) := by
      have h1 : Real.sqrt (10 * Cpw + 1) * (1 + HkSq)
          ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (1 + HkSq) :=
        mul_le_mul_of_nonneg_right hBle hCnn
      have h2 := mul_le_mul_of_nonneg_right h1 hs0
      nlinarith [h2]
    have hCs : (1 + HkSq) * α ^ (-(1 : ℝ)) ≤ (1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3 :=
      mul_le_mul_of_nonneg_left hs3 hCnn
    have hBCs : (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3) :=
      mul_le_mul_of_nonneg_left hCs (by nlinarith [Real.sqrt_nonneg (10 * Cpw + 1)])
    calc (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) := hA'
      _ ≤ (1 + K0 + K4)
            * ((Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hBC hDnn
      _ ≤ (1 + K0 + K4)
            * ((Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3)) :=
          mul_le_mul_of_nonneg_left hBCs hDnn
      _ = (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
            * ((1 + K0 + K4) * (1 + HkSq)) := by
          ring
  calc Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by linarith)
    _ ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
          * ((1 + K0 + K4) * (1 + HkSq)) :=
        hfinal

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
