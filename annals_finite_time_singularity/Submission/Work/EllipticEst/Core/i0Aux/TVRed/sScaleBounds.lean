import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real

/-- With `L = sScale P E = (P / (16 (P + E)))^{1/4}` and `η = 99/100`, the hypothesis
`F₀² + F₁² ≤ 4 L^{3+η} E + 200 L^{η-1} P` gives, after multiplying by `L^{1-η}`,
`(F₀² + F₁²) L^{1-η} ≤ 4 L⁴ E + 200 P ≤ (1/4) P + 200 P ≤ 201 P`. -/
theorem sScaleBounds {P E F₀ F₁ Cb : ℝ} (hP : 0 < P) (hE : 0 ≤ E) (hCb : 0 < Cb)
    (hS : F₀ ^ 2 + F₁ ^ 2
      ≤ 4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P) :
    (1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
        * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
      ≤ 1000 * (Cb + 1) ^ 2 * 201 * P) ∧
    (1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
        * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))
      ≤ 1000 * (Cb + 1) ^ 2 * 3204 * (P + E)) := by
  have hL := sScale_pos hP hE
  have hA := sScale_mul_A hP hE
  have hB := sScale_mul_B hP hE
  have hC := sScale_mul_C hP hE
  have hD := sScale_mul_D hP hE
  have h4 := sScale_rpow_four hP hE
  have hcoef : 0 ≤ 1000 * (Cb + 1) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  -- the first exponent: multiply through by `L ^ (1 - η) ≥ 0`
  have key1 : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
        ^ (1 - Work.Spaces.eta) ≤ 201 * P := by
    have h := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hL.le (1 - Work.Spaces.eta))
    have hkey : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
          ^ (1 - Work.Spaces.eta) ≤ 4 * E * (P / (16 * (P + E))) + 200 * P := by
      calc (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
          ≤ (4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
              + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta) := h
        _ = 4 * E * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta))
            + 200 * P * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)) := by ring
        _ = 4 * E * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (4 : ℝ) + 200 * P * 1 := by
              rw [hA, hB]
        _ = 4 * E * (P / (16 * (P + E))) + 200 * P := by rw [h4, mul_one]
    have hfin : 4 * E * (P / (16 * (P + E))) + 200 * P ≤ 201 * P := by
      have hden : (0 : ℝ) < 4 * (P + E) := by nlinarith
      have hsplit : 4 * E * (P / (16 * (P + E))) = P * E / (4 * (P + E)) := by
        field_simp
        ring
      have h1 : P * E / (4 * (P + E)) ≤ P / 4 := by
        rw [div_le_iff₀ hden]
        nlinarith
      linarith
    linarith
  -- the second exponent: multiply through by `L ^ (-(3 + η)) ≥ 0`
  have key2 : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
        ^ (-(3 + Work.Spaces.eta)) ≤ 3204 * (P + E) := by
    have h := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hL.le (-(3 + Work.Spaces.eta)))
    have hkey : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
          ^ (-(3 + Work.Spaces.eta)) ≤ 4 * E + 200 * P * (16 * (P + E) / P) := by
      calc (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
            ^ (-(3 + Work.Spaces.eta))
          ≤ (4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
              + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta)) := h
        _ = 4 * E * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta)))
            + 200 * P * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))) := by ring
        _ = 4 * E + 200 * P * (16 * (P + E) / P) := by
              rw [mul_comm ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)) _,
                hC, mul_one,
                mul_comm ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)) _,
                hD]
    have hfin : 4 * E + 200 * P * (16 * (P + E) / P) ≤ 3204 * (P + E) := by
      have hsplit : 200 * P * (16 * (P + E) / P) = 3200 * (P + E) := by
        field_simp
        ring
      linarith
    linarith
  constructor
  · calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (201 * P) := mul_le_mul_of_nonneg_left key1 hcoef
      _ = 1000 * (Cb + 1) ^ 2 * 201 * P := by ring
  · calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (3204 * (P + E)) := mul_le_mul_of_nonneg_left key2 hcoef
      _ = 1000 * (Cb + 1) ^ 2 * 3204 * (P + E) := by ring

end Work.EllipticEst.Core.i0Aux.TVRed
