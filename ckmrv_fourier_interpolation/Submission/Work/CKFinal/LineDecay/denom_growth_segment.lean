import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.divisor_qdiff_lower
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.CKFinal.LineDecay.qParamFun_line_norm_sub

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- For `w` with `Im w = 1` and `|Re w| ≤ 1` the point `S • w = -1/w` has imaginary part
in the interval `[1/2, 1]`: indeed `Im (S • w) = Im w / ‖w‖² = 1 / (Re w)² + 1`. -/
lemma S_smul_im_bounds (w : ℍ) (hw : w.im = 1) (hwr : |w.re| ≤ 1) :
    1 / 2 ≤ (ModularGroup.S • w).im ∧ (ModularGroup.S • w).im ≤ 1 := by
  have hns : Complex.normSq (w : ℂ) = w.re ^ 2 + 1 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hw]; ring
  have hre : w.re ^ 2 ≤ 1 := by
    rcases abs_le.mp hwr with ⟨h1, h2⟩
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - w.re)
      (by linarith : (0 : ℝ) ≤ 1 + w.re)]
  have him : (ModularGroup.S • w).im = 1 / Complex.normSq (w : ℂ) := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_S, hw]
  rw [him, hns]
  have hpos : (0 : ℝ) < w.re ^ 2 + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_one hpos]; nlinarith [sq_nonneg w.re]

/-- The CKMRV divisor `Δ(S • w)·(j τ - j (S • w))` is bounded *below* by `c · e^{2π Im τ}` when
`τ` lies on one of the two lines `Re τ = ±1/2` and `w = x + i` with `|x| ≤ 1`.

This is the sharp form needed to turn the CKMRV quotient bound
`‖z²K_±(τ,S•z)‖ ≤ C(1+‖τ‖)^A(1+‖z‖)^A e^{-π Im z}/‖Δ z (j τ - j z)‖` (at `z = S • w`) into a
bound with decay `e^{-2π Im τ}`: since `S • w` has `Im = 1/‖w‖² ∈ [1/2,1]`, `‖q(S•w)‖ ≥ e^{-2π}`
while `q(τ) = -e^{-2π Im τ}` on the lines, so `‖q τ - q(S•w)‖ ≥ e^{-2π} - e^{-4π} ≥ e^{-2π}/2` for
`Im τ ≥ 2`; `Work.Asymptotics.divisor_qdiff_lower` gives
`c₁‖q τ - q z‖ ≤ ‖Δ τ Δ z (j τ - j z)‖`, and `Work.Asymptotics.delta_upper_third`
(`‖Δ τ‖ ≤ C ‖q τ‖` for `Im τ ≥ 1/3`) converts the `Δ τ` factor. -/
theorem denom_growth_segment :
    ∃ c Y₀ : ℝ, 0 < c ∧ 1 ≤ Y₀ ∧
      ∀ (τ w : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        w.im = 1 → |w.re| ≤ 1 →
        c * Real.exp (2 * Real.pi * τ.im)
          ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • w)
              * (Work.Kernels.jInvariantFun τ
                  - Work.Kernels.jInvariantFun (ModularGroup.S • w))‖ := by
  obtain ⟨c₁, T₀, hc₁, _hT₀, hdq⟩ := Work.Asymptotics.divisor_qdiff_lower
  obtain ⟨C, hC, hUp⟩ := Work.Asymptotics.delta_upper_third
  refine ⟨c₁ * (Real.exp (-(2 * Real.pi)) / 2) / C, max T₀ 2, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hc₁ (by positivity)) hC
  · exact le_trans (by norm_num) (le_max_right _ _)
  intro τ w _hτ hY hwim hwr
  have hzim := S_smul_im_bounds w hwim hwr
  have hτT : T₀ ≤ τ.im := le_trans (le_max_left _ _) hY
  have hτ2 : (2 : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hY
  have hτ13 : 1 / 3 ≤ τ.im := by linarith
  -- The `z`-dependent part of the argument, uniform in `z` with `z.im ∈ [1/2, 1]`.
  have key : ∀ z : ℍ, 1 / 2 ≤ z.im → z.im ≤ 1 →
      c₁ * (Real.exp (-(2 * Real.pi)) / 2) / C * Real.exp (2 * Real.pi * τ.im)
        ≤ ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    intro z hz1 hz2
    set L : ℝ := ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hL
    have hLnn : 0 ≤ L := by rw [hL]; exact norm_nonneg _
    have hz13 : 1 / 3 ≤ z.im := by linarith
    have hdiv := hdq τ z hτT hz13
    have hdiv' : c₁ * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.DeltaFun τ‖ * L := by
      rw [hL]
      calc c₁ * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
          ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := hdiv
        _ = ‖Work.Kernels.DeltaFun τ‖
              * ‖Work.Kernels.DeltaFun z
                  * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
            simp only [norm_mul]; ring
    have hqz_low : Real.exp (-(2 * Real.pi)) ≤ ‖Work.Kernels.qParamFun z‖ := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_exp]
      nlinarith [Real.pi_pos, hz2]
    have hnq_low : Real.exp (-(2 * Real.pi)) / 2
        ≤ ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ := by
      have hhalf : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
        have hexp : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
          have h2 : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
          have h3 : (2 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (2 : ℝ); linarith
          exact le_trans h3 (Real.exp_le_exp.mpr h2)
        have hmul := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-(2 * Real.pi))).le
        rw [← Real.exp_add] at hmul
        rw [show 2 * Real.pi + -(2 * Real.pi) = 0 by ring, Real.exp_zero] at hmul
        linarith
      have hτexp : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) / 2 := by
        have h4 : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(4 * Real.pi)) := by
          rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ2]
        have hsplit : Real.exp (-(4 * Real.pi))
            = Real.exp (-(2 * Real.pi)) * Real.exp (-(2 * Real.pi)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h5 : Real.exp (-(2 * Real.pi)) * Real.exp (-(2 * Real.pi))
            ≤ Real.exp (-(2 * Real.pi)) / 2 := by
          have := mul_le_mul_of_nonneg_left hhalf (Real.exp_pos (-(2 * Real.pi))).le
          linarith
        calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(4 * Real.pi)) := h4
          _ = Real.exp (-(2 * Real.pi)) * Real.exp (-(2 * Real.pi)) := hsplit
          _ ≤ Real.exp (-(2 * Real.pi)) / 2 := h5
      have htri : ‖Work.Kernels.qParamFun z‖ - ‖Work.Kernels.qParamFun τ‖
          ≤ ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ := by
        have h := norm_sub_norm_le (Work.Kernels.qParamFun z) (Work.Kernels.qParamFun τ)
        rwa [norm_sub_rev] at h
      have hqτ : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
        Work.Asymptotics.norm_qParamFun τ
      linarith [hqz_low, hτexp, htri, hqτ]
    have hUp' : ‖Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [← Work.Asymptotics.norm_qParamFun τ]
      exact hUp τ hτ13
    have hstep : c₁ * (Real.exp (-(2 * Real.pi)) / 2)
        ≤ C * Real.exp (-(2 * Real.pi * τ.im)) * L := by
      have h1 : c₁ * (Real.exp (-(2 * Real.pi)) / 2)
          ≤ c₁ * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ :=
        mul_le_mul_of_nonneg_left hnq_low hc₁.le
      have h3 : ‖Work.Kernels.DeltaFun τ‖ * L
          ≤ C * Real.exp (-(2 * Real.pi * τ.im)) * L :=
        mul_le_mul_of_nonneg_right hUp' hLnn
      linarith [h1, hdiv', h3]
    have hkey : c₁ * (Real.exp (-(2 * Real.pi)) / 2) * Real.exp (2 * Real.pi * τ.im)
        ≤ C * L := by
      have hmul := mul_le_mul_of_nonneg_left hstep (Real.exp_pos (2 * Real.pi * τ.im)).le
      have h1 : (C * Real.exp (-(2 * Real.pi * τ.im)) * L) * Real.exp (2 * Real.pi * τ.im)
          = C * L := by
        have h2 : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
          rw [← Real.exp_add]
          rw [show -(2 * Real.pi * τ.im) + 2 * Real.pi * τ.im = 0 by ring, Real.exp_zero]
        calc (C * Real.exp (-(2 * Real.pi * τ.im)) * L) * Real.exp (2 * Real.pi * τ.im)
            = C * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im)) * L := by
              ring
          _ = C * 1 * L := by rw [h2]
          _ = C * L := by ring
      linarith [hmul, h1]
    rw [hL] at hkey ⊢
    rw [div_mul_eq_mul_div, div_le_iff₀ hC, mul_comm L C]
    exact hkey
  exact key (ModularGroup.S • w) hzim.1 hzim.2

end Work.CKFinal.LineDecay
