import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.arithNsumG3Mul =====
section

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
end
-- ===== merged: Submission.Work.Spaces.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The domain and the fundamental parameters -/

/-- The half-line `[0,∞)` of the self-similar radial variable `z`. -/
def Iz : Set ℝ := Set.Ici 0

/-- The angular interval `[0,π/2]`. -/
def Iθ : Set ℝ := Set.Icc 0 (π/2)

/-- The domain `[0,∞) × [0,π/2]` of the self-similar variables `(z,θ)`. -/
def Dom : Set (ℝ × ℝ) := Iz ×ˢ Iθ

/-- The exponent `η = 99/100` of the paper. -/
def eta : ℝ := 99/100

/-- The exponent `γ = 1 + α/10` of the paper. -/
def gam (α : ℝ) : ℝ := 1 + α / 10

/-! ## Weights and angular data -/

/-- The radial weight `w(z) = (1+z)²/z²`.  (At `z = 0` Lean's totalised division
gives the value `0`, which is irrelevant since `{0}` is a null set.) -/
def w (z : ℝ) : ℝ := (1 + z) ^ 2 / z ^ 2

/-- The angular weight `w_θ(θ) = 1 / sin(2θ)^{γ/2}`. -/
def wTheta (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(gam α / 2))

/-- The product weight `W = w · w_θ`. -/
def Wt (α : ℝ) (z θ : ℝ) : ℝ := w z * wTheta α θ

/-- `Γ(θ) = (sin θ · cos²θ)^{α/3}`. -/
def Gam (α θ : ℝ) : ℝ := (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)

/-- `K(θ) = 3 sin θ cos²θ`. -/
def K (θ : ℝ) : ℝ := 3 * Real.sin θ * Real.cos θ ^ 2

/-- The normalisation constant `c(α) = ∫₀^{π/2} Γ(θ) K(θ) dθ` of the paper.
The paper always uses it in the range `1/10 ≤ c ≤ 10`; this is proved in
`Work.Spaces.Weights.c_bounds` for `0 < α ≤ 1`. -/
def c (α : ℝ) : ℝ := ∫ θ in Iθ, Gam α θ * K θ

/-! ## The differential operators `D_z`, `D_θ` (and their plain counterparts) -/

/-- The plain partial derivative `∂_z f`. -/
def pz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => deriv (fun z' => f z' θ) z

/-- The plain partial derivative `∂_θ f`. -/
def pth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => deriv (fun θ' => f z θ') θ

/-- The operator `D_z f = z ∂_z f`. -/
def Dz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * pz f z θ

/-- The operator `D_θ f = sin(2θ) ∂_θ f`. -/
def Dth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * pth f z θ

/-- Iterated `∂_z`. -/
def pzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => pz (pzIter n f)

/-- Iterated `∂_θ`. -/
def pthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => pth (pthIter n f)

/-- Iterated `D_z`. -/
def DzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dz (DzIter n f)

/-- Iterated `D_θ`. -/
def DthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth (DthIter n f)

/-- The mixed operator `D_z^j D_θ^i f` of the paper. -/
def mixed (j i : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := DzIter j (DthIter i f)

@[simp] theorem pzIter_zero (f : ℝ → ℝ → ℝ) : pzIter 0 f = f := rfl
@[simp] theorem pzIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : pzIter (n + 1) f = pz (pzIter n f) := rfl
@[simp] theorem pthIter_zero (f : ℝ → ℝ → ℝ) : pthIter 0 f = f := rfl
@[simp] theorem pthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : pthIter (n + 1) f = pth (pthIter n f) := rfl
@[simp] theorem DzIter_zero (f : ℝ → ℝ → ℝ) : DzIter 0 f = f := rfl
@[simp] theorem DzIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : DzIter (n + 1) f = Dz (DzIter n f) := rfl
@[simp] theorem DthIter_zero (f : ℝ → ℝ → ℝ) : DthIter 0 f = f := rfl
@[simp] theorem DthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : DthIter (n + 1) f = Dth (DthIter n f) := rfl
@[simp] theorem mixed_zero_left (i : ℕ) (f : ℝ → ℝ → ℝ) : mixed 0 i f = DthIter i f := rfl
@[simp] theorem mixed_zero_right (j : ℕ) (f : ℝ → ℝ → ℝ) : mixed j 0 f = DzIter j f := rfl

/-! ## The squared `L²` functional, the `H^k` norm -/

/-- The squared `L²`-norm of `g` over `[0,∞) × [0,π/2]` w.r.t. `dz dθ`. -/
def L2Sq (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Iz, ∫ θ in Iθ, (g z θ) ^ 2

/-- The integrand whose (iterated) integral is the square of the `H^k` norm of `f`:
the sum of the squares of all the weighted derivatives appearing in `HkNorm` of the
paper.  Taking it as a single sum keeps the bookkeeping of the norm in one place. -/
def HkIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0

/-- The square of the `H^k`-norm of `f`:
`|f|²_{H^k} = ∑_{i=0}^k |D_z^i f · w / sin(2θ)^{η/2}|²_{L²}
 + ∑_{0 ≤ i+j ≤ k, i ≥ 1} |D_z^j D_θ^i f · W|²_{L²}`. -/
def HkSq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Iz, ∫ θ in Iθ, HkIntegrand α k f z θ

/-- The `H^k`-norm of the paper (the square root of `HkSq`). -/
def HkNorm (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ := Real.sqrt (HkSq α k f)

/-- Membership in `H^k`: on the domain, all the weighted derivatives occurring in `HkSq`
give honest (integrable) iterated integrals.  Under this hypothesis `HkSq α k f` is the
sum of the squared `L²`-norms of the paper, and `HkNorm α k f` is finite.
(Only `z ∈ Iz` is required: nothing is assumed about `f` for `z < 0`.) -/
def HkMem (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α k f z θ) Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) Iz

/-! ## Suprema on the domain, and the `W^{l,∞}`-norm -/


/-- The supremum of `|g|` over the domain `[0,∞) × [0,π/2]`, i.e. the `L^∞`-norm of
`g` on the domain. -/
def supAbs (g : ℝ → ℝ → ℝ) : ℝ := sSup {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = |g z θ|}

/-- `⟨|g|⟩` is bounded on the domain `[0,∞) × [0,π/2]`: the supremum `supAbs g` is then
the honest `L^∞`-norm of `g` rather than the junk value `0` attached to an unbounded set. -/
def SupFinite (g : ℝ → ℝ → ℝ) : Prop := BddAbove {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = |g z θ|}

/-- The `W^{l,∞}`-norm of the paper:
`|f|_{𝒲^{l,∞}} = ∑_{0≤k≤l} |(z+1)^k ∂_z^k f|_{L∞}
 + ∑_{1≤k+j≤l, j≥1} |(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α+sin(2θ))|_{L∞}`. -/
def WlInf (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ))
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0

/-- Membership in `W^{l,∞}`: every one of the finitely many suprema occurring in
`WlInf` is that of a bounded function, so that `WlInf` is the honest sum of sup norms. -/
def WlInfMem (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ k ≤ l, SupFinite (fun z θ => (z + 1) ^ k * pzIter k f z θ)) ∧
    ∀ j ≤ l, ∀ k ≤ l, 1 ≤ j → k + j ≤ l →
      SupFinite (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))

/-! ## Regularity and boundary hypotheses used by the estimates

Two smoothness classes are provided.  `SmoothNbhd` is the strongest and easiest to
use: `f` is smooth on an open set containing the closed quadrant, so all the
one-sided boundary conditions needed by the fundamental theorem of calculus are
automatic.  `SmoothInt` only requires smoothness on the open quadrant together with
smoothness in `z` down to `z = 0` at every angle; it contains the basic `W^{l,∞}`
function `Γ(θ)·z/(1+z)²`, which is *not* smooth at the angular boundary when
`α/3 ∉ ℕ`.  All Leibniz manipulations for `D_z`, `D_θ` are valid in `SmoothInt`,
because both operators carry a factor (`z` resp. `sin(2θ)`) which vanishes on the
boundary of the quadrant. -/

/-- `f` is smooth on an open neighbourhood of the closed quadrant `[0,∞) × [0,π/2]`. -/
def SmoothNbhd (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1))

/-- `f` is smooth on the open strip `(-1,∞) × (0,π/2)` and, for every angle
`θ ∈ [0,π/2]`, smooth in `z` on a right-neighbourhood of `0`. -/
def SmoothInt (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π/2)) ∧
    ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1))

/-- `f` and all its iterated plain partial derivatives `∂_z^j ∂_θ^i f` with `i+j ≤ n`
tend to `0` as `z → ∞`, for each fixed angle `θ ∈ [0,π/2]`. -/
def DecayInZ (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ j i : ℕ, i + j ≤ n → ∀ θ ∈ Iθ,
    Tendsto (fun z => pzIter j (pthIter i f) z θ) atTop (𝓝 0)

/-- Every mixed `D`-derivative `D_z^b D_θ^a f` with `a + b ≤ n` tends to `0` as `z → ∞`,
for every angle `θ ∈ [0,π/2]`.  This is the decay hypothesis needed by the Hardy
inequalities when they are applied to `D`-iterates of `f` (it is *not* implied by the
pointwise decay of the plain partial derivatives, since `D_z = z∂_z` carries a factor
`z`); it holds for every compactly supported function and for every function whose
partial derivatives decay at least like powers of `z`. -/
def DecayMixed (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℕ, a + b ≤ n → ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a f z θ) atTop (𝓝 0)

/-- The decay hypotheses used by the product rules in `H^4` and `𝒲^{4,∞}`: all plain
partial derivatives `∂_z^j ∂_θ^i f` and all mixed `D`-derivatives `D_z^b D_θ^a f` with
`i + j ≤ n` resp. `a + b ≤ n` tend to `0` as `z → ∞`, for every angle `θ ∈ [0,π/2]`.
Compactly supported functions and functions whose derivatives decay like powers satisfy
this; it is exactly the decay needed by the Hardy inequalities of §H2. -/
def DecayAll (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop := DecayInZ n f ∧ DecayMixed n f

/-- `f` vanishes identically on the two angular boundaries `θ = 0` and `θ = π/2`. -/
def VanishTheta (f : ℝ → ℝ → ℝ) : Prop := (∀ z : ℝ, f z 0 = 0) ∧ (∀ z : ℝ, f z (π / 2) = 0)

/-! ## Elementary consequences of the definitions -/

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem eta_nonneg : 0 ≤ eta := le_of_lt eta_pos

theorem gam_sub_one (α : ℝ) : gam α - 1 = α / 10 := by simp [gam]
theorem one_lt_gam {α : ℝ} (hα : 0 < α) : 1 < gam α := by
  have : 0 < α / 10 := by linarith
  linarith [gam_sub_one α]
theorem gam_pos {α : ℝ} (hα : 0 < α) : 0 < gam α := by linarith [one_lt_gam hα]

theorem zero_mem_Iz : (0 : ℝ) ∈ Iz := by simp [Iz]
theorem zero_mem_Iθ : (0 : ℝ) ∈ Iθ := by
  refine ⟨le_refl 0, ?_⟩
  have := Real.pi_pos; linarith
theorem pi_half_mem_Iθ : (π / 2) ∈ Iθ := by
  refine ⟨?_, le_refl _⟩
  have := Real.pi_pos; linarith

/-- The `H^k` integrand is a sum of squares, hence nonnegative. -/
theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ HkIntegrand α k f z θ := by
  rw [HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ HkSq α k f :=
  integral_nonneg fun z => integral_nonneg fun θ => HkIntegrand_nonneg α k f z θ

theorem HkNorm_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ HkNorm α k f :=
  Real.sqrt_nonneg _




theorem supAbs_le {g : ℝ → ℝ → ℝ} {C : ℝ} (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |g z θ| ≤ C) :
    supAbs g ≤ C :=
  csSup_le ⟨|g 0 0|, 0, zero_mem_Iz, 0, zero_mem_Iθ, rfl⟩ fun y hy => by
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ

/-- Pointwise bound from the `L^∞`-norm, assuming the latter is honest. -/
theorem abs_le_supAbs {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : SupFinite g) : |g z θ| ≤ supAbs g :=
  le_csSup h ⟨z, hz, θ, hθ, rfl⟩


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.cs_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory
open scoped RealInnerProductSpace

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the Lebesgue integral over a set, in the special
case of exponent `2`: for real functions `u`, `v` that are square-integrable on `s`,
`(∫_s u v)^2 ≤ (∫_s u^2) * (∫_s v^2)`.

The proof passes to the `L²` space `Lp ℝ 2 (volume.restrict s)`, which is an inner product space
whose inner product is the integral of the pointwise inner product, and applies the abstract
Cauchy–Schwarz inequality `real_inner_mul_inner_self_le` there, then transfers the four integrals
back along the `MemLp.toLp` a.e.-equalities. -/
theorem cs_integral {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2 ≤ (∫ x in s, u x ^ 2) * (∫ x in s, v x ^ 2) := by
  have hB : (∫ x in s, u x * v x) = ∫ a in s, (hu.toLp u) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x in s, u x ^ 2) = ∫ a in s, (hu.toLp u) a * (hu.toLp u) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x in s, v x ^ 2) = ∫ a in s, (hv.toLp v) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.integrableOn_majorant_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set

/-- The function `θ ↦ (π/4)^p * (θ^(-p) + (π/2 - θ)^(-p))` is integrable on `[0, π/2]`
for `p ∈ (0,1)`: both singular terms are `rpow`-integrable since the exponent `-p`
satisfies `-1 < -p`. -/
theorem integrableOn_majorant_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  have hp : -1 < -p := by linarith
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (-p)) (Set.Icc 0 (Real.pi / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hpi]
    exact intervalIntegral.intervalIntegrable_rpow' hp
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-p)) (Set.Icc 0 (Real.pi / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hpi]
    simpa using
      (IntervalIntegrable.comp_sub_left_iff (f := fun θ : ℝ => θ ^ (-p)) (Real.pi / 2)
        (a := Real.pi / 2) (b := 0)).mpr
        (intervalIntegral.intervalIntegrable_rpow' hp).symm
  have hsum : MeasureTheory.IntegrableOn
      (fun θ : ℝ => θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) (Set.Icc 0 (Real.pi / 2)) :=
    h1.add h2
  exact hsum.const_mul ((Real.pi / 4) ^ p)

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.integrable_prod_of_iterated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

theorem integrable_prod_of_iterated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    {G : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ G a b)
    (hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => G a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, G a b ∂ν) μ) :
    MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) ∧
      ∫ p, G p.1 p.2 ∂(μ.prod ν) = ∫ a, (∫ b, G a b ∂ν) ∂μ := by
  -- Pointwise nonnegativity turns the norm in `integrable_prod_iff` into `G` itself.
  have hkey : (fun x : α => ∫ y, ‖Function.uncurry G (x, y)‖ ∂ν) =
      (fun x => ∫ y, G x y ∂ν) := by
    funext x
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => by
        simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (hnn x y)])
  have hIntegrable : MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) := by
    rw [MeasureTheory.integrable_prod_iff hAE]
    exact ⟨hslice, by rw [hkey]; exact houter⟩
  exact ⟨hIntegrable, (MeasureTheory.integral_integral hIntegrable).symm⟩

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.integral_majorant_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set intervalIntegral

namespace Work.Spaces

/-- Evaluating the majorant integral of `sin_rpow_le_majorant`:
for `0 < p < 1` one has
`∫₀^{π/2} (π/4)^p (θ^{-p} + (π/2 - θ)^{-p}) dθ = π (1/2)^p / (1 - p)`. -/
theorem integral_majorant_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ θ in Set.Icc (0 : ℝ) (π / 2), ((π / 4) ^ p * (θ ^ (-p) + (π / 2 - θ) ^ (-p)))
      = π * (1 / 2) ^ p / (1 - p) := by
  have h0le : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hp : -1 < -p := by linarith
  -- Integrability of the two summands on `[0, π/2]`.
  have hf : IntervalIntegrable (fun x : ℝ => x ^ (-p)) volume (0 : ℝ) (π / 2) :=
    intervalIntegrable_rpow' hp
  have hg : IntervalIntegrable (fun x : ℝ => (π / 2 - x) ^ (-p)) volume (0 : ℝ) (π / 2) := by
    have h := (hf.comp_sub_left (π / 2)).symm
    simpa using h
  -- `∫₀^{π/2} θ^{-p} dθ = (π/2)^{1-p} / (1 - p)`.
  have h1 : (∫ θ in (0 : ℝ)..(π / 2), θ ^ (-p)) = (π / 2) ^ (1 - p) / (1 - p) := by
    rw [integral_rpow (Or.inl hp)]
    rw [show (-p + 1 : ℝ) = 1 - p by ring]
    rw [Real.zero_rpow (by intro h; linarith)]
    ring
  -- The reflected integral is the same by the substitution `θ ↦ π/2 - θ`.
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (π / 2 - θ) ^ (-p)) = (π / 2) ^ (1 - p) / (1 - p) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-p)) (π / 2)]
    simp only [sub_self, sub_zero]
    exact h1
  -- Pass from the set integral over `Icc 0 (π/2)` to the interval integral `0..π/2`.
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0le]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hf hg, h1, h2]
  -- Pure `rpow` bookkeeping: `(π/2)^{1-p} = (π/2) · ((π/2)^p)⁻¹`, and
  -- `(π/4)^p · ((π/2)^p)⁻¹ = (1/2)^p`.
  have h2p : (π / 2 : ℝ) ^ (1 - p) = (π / 2) * ((π / 2) ^ p)⁻¹ := by
    rw [show (1 : ℝ) - p = 1 + (-p) by ring, Real.rpow_add (by linarith [Real.pi_pos]),
      Real.rpow_one, Real.rpow_neg (by linarith [Real.pi_pos])]
  have h3 : (π / 4 : ℝ) ^ p * ((π / 2) ^ p)⁻¹ = (1 / 2 : ℝ) ^ p := by
    rw [← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by positivity) p]
    congr 1
    field_simp
    ring
  have hmain : (π / 4) ^ p * (2 * (π / 2) ^ (1 - p)) = π * (1 / 2) ^ p := by
    rw [h2p]
    calc (π / 4) ^ p * (2 * ((π / 2) * ((π / 2) ^ p)⁻¹))
        = 2 * ((π / 2) * ((π / 4) ^ p * ((π / 2) ^ p)⁻¹)) := by ring
      _ = 2 * ((π / 2) * (1 / 2) ^ p) := by rw [h3]
      _ = π * (1 / 2) ^ p := by ring
  have key : (2 * (π / 4) ^ p * (π / 2) ^ (1 - p)) = π * (1 / 2) ^ p := by
    rw [show (2 : ℝ) * (π / 4) ^ p * (π / 2) ^ (1 - p)
        = (π / 4) ^ p * (2 * (π / 2) ^ (1 - p)) by ring]
    exact hmain
  have e1 : (π / 2) ^ (1 - p) / (1 - p) + (π / 2) ^ (1 - p) / (1 - p)
      = 2 * ((π / 2) ^ (1 - p) / (1 - p)) := by ring
  have e2 : (π / 4) ^ p * (2 * ((π / 2) ^ (1 - p) / (1 - p)))
      = (2 * (π / 4) ^ p * (π / 2) ^ (1 - p)) / (1 - p) := by ring
  rw [e1, e2, key]

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.pzIter_hKer_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.Spaces

set_option autoImplicit false

/-! ## The closed form of the `k`-th derivative -/

/-- The closed form of the `k`-th derivative of `z ↦ z/(1+z)²`:
`(-1)^k k! (z-k) (1+z)^{-(k+2)}`, written with `(1+z)⁻¹`. -/
noncomputable def hKerClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1) ^ k * (k.factorial : ℝ)) * ((z - k) * ((1 + z)⁻¹) ^ (k + 2))

/-- `(1+z)^{-(k+2)} = (1+z)·(1+z)^{-(k+3)}` for `1+z ≠ 0`. -/
lemma hKerClosed_shift (k : ℕ) (z : ℝ) (hz : (1 + z) ≠ 0) :
    ((1 + z)⁻¹) ^ (k + 2) = (1 + z) * ((1 + z)⁻¹) ^ (k + 3) := by
  have hu : (1 + z) * ((1 + z)⁻¹) = 1 := mul_inv_cancel₀ hz
  have h1 : ((1 + z)⁻¹) ^ (k + 3) = ((1 + z)⁻¹) ^ (k + 2) * ((1 + z)⁻¹) := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
  rw [h1, mul_comm (((1 + z)⁻¹) ^ (k + 2)) ((1 + z)⁻¹), ← mul_assoc, hu, one_mul]

/-- `(1+z)^{-(k+1)}·(-(1+z)^{-2}) = -(1+z)^{-(k+3)}`. -/
lemma hKerClosed_neg_pow (k : ℕ) (z : ℝ) :
    ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2)) = -((1 + z)⁻¹) ^ (k + 3) := by
  rw [mul_neg, ← pow_add, show (k + 1) + 2 = k + 3 by omega]

/-- The value of the derivative of the closed form: if
`D_k(z) = (-1)^k k! (z-k)(1+z)^{-(k+2)}` then
`D_k'(z) = D_{k+1}(z) = (-1)^{k+1}(k+1)! (z-(k+1))(1+z)^{-(k+3)}`. -/
lemma hKerClosed_step (k : ℕ) (z : ℝ) (hz : (1 + z) ≠ 0) :
    (-1) ^ k * (k.factorial : ℝ) *
        (1 * ((1 + z)⁻¹) ^ (k + 2)
          + (z - (k : ℝ)) * ((↑(k + 2)) * ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2))))
      = hKerClosed (k + 1) z := by
  have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp2 : (↑(k + 2) : ℝ) * ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2)) =
      -((↑(k + 2)) * ((1 + z)⁻¹) ^ (k + 3)) := by
    rw [mul_assoc, hKerClosed_neg_pow k z, mul_neg]
  unfold hKerClosed
  rw [hsign, hfact, one_mul, hKerClosed_shift k z hz, hp2]
  push_cast
  ring

/-- The closed form has the expected derivative. -/
lemma hasDerivAt_hKerClosed (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (hKerClosed k) (hKerClosed (k + 1) z) z := by
  have hz' : (1 + z) ≠ 0 := by intro h; apply hz; linarith
  have h1 : HasDerivAt (fun t : ℝ => t - (k : ℝ)) 1 z := by
    simpa using (hasDerivAt_id z).sub_const (k : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv := hh.inv hz'
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have hp := h2.pow (k + 2)
  have hmul := h1.mul hp
  have hc := hmul.const_mul ((-1) ^ k * (k.factorial : ℝ))
  have hfun :
      (fun y : ℝ => (-1) ^ k * (k.factorial : ℝ) *
        ((fun t : ℝ => t - (k : ℝ)) * (fun t : ℝ => (1 + t)⁻¹) ^ (k + 2)) y)
        = hKerClosed k := by
    funext y; simp only [hKerClosed, Pi.mul_apply, Pi.pow_apply]
  have hv2 : (-1) ^ k * (k.factorial : ℝ) *
      (1 * ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 2)) z
        + (z - (k : ℝ)) * (↑(k + 2) * (1 + z)⁻¹ ^ (k + 2 - 1) * (-((1 + z)⁻¹) ^ 2)))
      = hKerClosed (k + 1) z := by
    simp only [Pi.pow_apply]
    rw [show k + 2 - 1 = k + 1 by omega]
    exact hKerClosed_step k z hz'
  rw [hfun, hv2] at hc
  exact hc

/-- The `k`-th derivative of `z ↦ z/(1+z)²` for `z > -1`. -/
theorem iter_deriv_hKerClosed : ∀ (k : ℕ) (z : ℝ),
    -1 < z → deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2) z = hKerClosed k z := by
  intro k
  induction k with
  | zero =>
    intro z _
    simp only [Function.iterate_zero, id_eq, hKerClosed, Nat.factorial_zero, Nat.cast_one,
      pow_zero, Nat.cast_zero, sub_zero, inv_pow, div_eq_mul_inv]
    ring
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hev : (deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2)) =ᶠ[𝓝 z] (hKerClosed k) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_hKerClosed k (by linarith)).deriv

/-! ## The weighted bound -/

theorem pzIter_hKer_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ (k.factorial : ℝ) * (k + 1) := by
  have hz1 : -1 < z := by linarith
  rw [iter_deriv_hKerClosed k z hz1]
  have hz' : (1 + z) ≠ 0 := by positivity
  have hUnn : 0 ≤ ((1 + z)⁻¹) ^ 2 := sq_nonneg _
  have hknn : 0 ≤ (k.factorial : ℝ) := by positivity
  have hpow2 : (z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 2) = ((1 + z)⁻¹) ^ 2 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, show (z + 1) = (1 + z) by ring,
      mul_inv_cancel₀ hz', one_pow, one_mul]
  have hval : (z + 1) ^ k * hKerClosed k z
      = ((-1) ^ k * (k.factorial : ℝ)) * ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ 2) := by
    rw [hKerClosed]
    rw [show (z + 1) ^ k * (((-1) ^ k * (k.factorial : ℝ)) *
          ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ (k + 2)))
        = ((-1) ^ k * (k.factorial : ℝ)) *
            ((z - (k : ℝ)) * ((z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 2))) by ring]
    rw [hpow2]
  rw [hval]
  have hmul1 : (1 + z) ^ 2 * ((1 + z)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz', one_pow]
  have hkey : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
    have h1 : |z - (k : ℝ)| ≤ z + (k : ℝ) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k, hz]
    have h2 : z + (k : ℝ) ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
      nlinarith [sq_nonneg z, Nat.cast_nonneg (α := ℝ) k, hz]
    linarith
  have hb : |z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2 ≤ (k : ℝ) + 1 := by
    calc |z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2
        ≤ (((k : ℝ) + 1) * (1 + z) ^ 2) * ((1 + z)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hUnn
      _ = ((k : ℝ) + 1) * ((1 + z) ^ 2 * ((1 + z)⁻¹) ^ 2) := by ring
      _ = (k : ℝ) + 1 := by rw [hmul1]; ring
  have habs : |((-1) ^ k * (k.factorial : ℝ)) * ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ 2)| =
      (k.factorial : ℝ) * (|z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul]
    have h1 : |((-1 : ℝ) ^ k)| = 1 := by rw [abs_pow]; norm_num
    rw [h1, abs_of_nonneg hknn, abs_of_nonneg hUnn]
    ring
  rw [habs]
  have := mul_le_mul_of_nonneg_left hb hknn
  simpa [Nat.cast_add, Nat.cast_one] using this

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.rpow_sup_ineq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces


end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.sin_rpow_le_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Spaces

/-- Core Jordan-type estimate: for `0 < p` and `x ∈ [0, π/4]`,
`(sin (2 x)) ^ (-p) ≤ (π/4) ^ p * x ^ (-p)`.

Jordan's inequality `(2/π) y ≤ sin y` on `[0, π/2]` applied to `y = 2 x` gives
`sin (2 x) ≥ (4/π) x`, and raising to the non-positive power `-p` reverses the
inequality. -/
private lemma sin_two_mul_rpow_le_of_le_pi_div_four (p x : ℝ) (hp : 0 < p)
    (hx : x ∈ Set.Icc (0 : ℝ) (π / 4)) :
    (Real.sin (2 * x)) ^ (-p) ≤ (π / 4) ^ p * x ^ (-p) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [mul_zero, Real.sin_zero, Real.zero_rpow (by linarith : (-p) ≠ 0), mul_zero]
  · have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ π / 2 := by linarith
    have hj := Real.mul_le_sin h2x0 h2x1
    have hjeq : 2 / π * (2 * x) = (4 / π) * x := by ring
    rw [hjeq] at hj
    have hpos : 0 < (4 / π) * x := by positivity
    have key := Real.rpow_le_rpow_of_nonpos hpos hj (show -p ≤ 0 by linarith)
    have hcoef : (4 / π : ℝ) ^ (-p) = (π / 4) ^ p := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / π),
          ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / π) p, inv_div]
    have hmr : ((4 / π) * x) ^ (-p) = (π / 4) ^ p * x ^ (-p) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / π) (le_of_lt h), hcoef]
    rw [hmr] at key
    exact key

theorem sin_rpow_le_majorant (p θ : ℝ) (hp : 0 < p) (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (π / 4) ^ p * (θ ^ (-p) + (π / 2 - θ) ^ (-p)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- The whole inequality is invariant under `θ ↦ π/2 - θ`, so reduce to `θ ≤ π/4`.
  rcases le_total θ (π / 4) with h | h
  · have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p θ hp ⟨hθ0, h⟩
    have h1 : θ ^ (-p) ≤ θ ^ (-p) + (π / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ π / 2 - θ) (-p))
    have hle : (π / 4) ^ p * θ ^ (-p) ≤
        (π / 4) ^ p * (θ ^ (-p) + (π / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ π / 4) p)
    linarith
  · have hsin : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
      have h2 : 2 * (π / 2 - θ) = π - 2 * θ := by ring
      rw [h2, Real.sin_pi_sub]
    have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p (π / 2 - θ) hp
      ⟨by linarith, by linarith⟩
    rw [hsin]
    have h1 : (π / 2 - θ) ^ (-p) ≤ θ ^ (-p) + (π / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_left (Real.rpow_nonneg hθ0 (-p))
    have hle : (π / 4) ^ p * (π / 2 - θ) ^ (-p) ≤
        (π / 4) ^ p * (θ ^ (-p) + (π / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ π / 4) p)
    linarith

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.sq_mul_div_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The key identity `(s^(e/2))^2 = s^e` for `0 < s`. -/
private lemma rpow_half_sq (s e : ℝ) (hs : 0 < s) :
    (s ^ (e / 2)) ^ 2 = s ^ e := by
  rw [sq, ← Real.rpow_add hs]
  congr 1
  ring

theorem sq_mul_div_rpow (A W s e : ℝ) (hs : 0 ≤ s) (he : e ≠ 0) :
    (A * (W / s ^ (e / 2))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  rcases hs.lt_or_eq with h | h
  · -- `0 < s`: reduce to `(s^(e/2))^2 = s^e` and clear inverses.
    rw [Real.rpow_neg hs e, ← rpow_half_sq s e h, ← inv_pow, div_eq_mul_inv]
    ring
  · -- `s = 0`: both sides vanish, since `e ≠ 0` forces `e/2 ≠ 0` and `-e ≠ 0`.
    subst h
    have he2 : e / 2 ≠ 0 := div_ne_zero he two_ne_zero
    have hne : -e ≠ 0 := neg_ne_zero.mpr he
    rw [Real.zero_rpow he2, div_zero, mul_zero, Real.zero_rpow hne]
    ring

end Work.Spaces
end
