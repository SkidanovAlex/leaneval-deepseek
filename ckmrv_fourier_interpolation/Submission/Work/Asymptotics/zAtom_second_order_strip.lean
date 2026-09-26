import Submission.Work.Asymptotics.funnel_tauAtom_second_order

namespace Work.Asymptotics

open UpperHalfPlane

/-!
# Second-order `q`-expansions of the atoms at a strip point

The five atoms `E₂,E₄,E₆,Δ,j` are functions of `q = qParamFun` alone, so the second-order
expansions proved for the funnel in `funnel_tauAtom_second_order` hold on the larger region
`1 ≤ Im z`, which is the form needed for the `z`-atoms of the funnel-bracket residual bound
(`-1 ≤ Re z ≤ 2`, `Im z = t ≥ Im τ + 1 ≥ 3`).  The assembly is a copy of the body of
`funnel_tauAtom_second_order`, whose only use of the funnel hypothesis is `Funnel.im_one`.
-/

/-- **Second-order `q`-expansions of the five atoms for `1 ≤ Im z`.** -/
theorem zAtom_second_order_strip :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z
          + 72 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 ∧
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 ∧
      ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
          + 16632 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 ∧
      ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z
          + 24 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 ∧
      ‖Work.Kernels.jInvariantFun z * Work.Kernels.qParamFun z - 1
          - 744 * Work.Kernels.qParamFun z
          - 196884 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C1, hC1, h1⟩ := E2Fun_second_order
  obtain ⟨C2, hC2, h2⟩ := E4Fun_second_order
  obtain ⟨C3, hC3, h3⟩ := E6Fun_second_order
  obtain ⟨C4, hC4, h4⟩ := DeltaFun_fourth_order
  obtain ⟨C5, hC5, h5⟩ := jqParam_second_order
  refine ⟨C1 + C2 + C3 + (C4 + 252) + C5 + 1, 0, by positivity, le_rfl, fun z hz => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    have h := norm_qParamFun_le z hz
    exact le_trans h (by rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos])
  have hq3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
  have hC1' : C1 ≤ C1 + C2 + C3 + (C4 + 252) + C5 + 1 := by linarith
  have hC2' : C2 ≤ C1 + C2 + C3 + (C4 + 252) + C5 + 1 := by linarith
  have hC3' : C3 ≤ C1 + C2 + C3 + (C4 + 252) + C5 + 1 := by linarith
  have hC4' : C4 + 252 ≤ C1 + C2 + C3 + (C4 + 252) + C5 + 1 := by linarith
  have hC5' : C5 ≤ C1 + C2 + C3 + (C4 + 252) + C5 + 1 := by linarith
  have hscale : (Work.Kernels.scale z) ^ (0:ℝ) = 1 := by rw [Real.rpow_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hscale, mul_one]
    calc ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z
          + 72 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ C1 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h1 z hz
      _ ≤ (C1 + C2 + C3 + (C4 + 252) + C5 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_right hC1' hq3
  · rw [hscale, mul_one]
    calc ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ C2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h2 z hz
      _ ≤ (C1 + C2 + C3 + (C4 + 252) + C5 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_right hC2' hq3
  · rw [hscale, mul_one]
    calc ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
          + 16632 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ C3 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h3 z hz
      _ ≤ (C1 + C2 + C3 + (C4 + 252) + C5 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_right hC3' hq3
  · rw [hscale, mul_one]
    have hsplit : Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z
          + 24 * (Work.Kernels.qParamFun z) ^ 2
        = (Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
              - 24 * (Work.Kernels.qParamFun z) ^ 2
              + 252 * (Work.Kernels.qParamFun z) ^ 3))
          + 252 * (Work.Kernels.qParamFun z) ^ 3 := by ring
    rw [hsplit]
    have h252 : ‖(252:ℂ) * (Work.Kernels.qParamFun z) ^ 3‖
        ≤ 252 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h4' : ‖Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
          - 24 * (Work.Kernels.qParamFun z) ^ 2
          + 252 * (Work.Kernels.qParamFun z) ^ 3)‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      refine le_trans (h4 z hz) ?_
      have h4e : ‖Work.Kernels.qParamFun z‖ ^ 4
          = (‖Work.Kernels.qParamFun z‖ ^ 3) * ‖Work.Kernels.qParamFun z‖ := by ring
      rw [h4e, ← mul_assoc]
      have h1 : (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * ‖Work.Kernels.qParamFun z‖
          ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * 1 :=
        mul_le_mul_of_nonneg_left hq1 (by positivity)
      simpa using h1
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add h4' h252) ?_
    rw [show C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 + 252 * ‖Work.Kernels.qParamFun z‖ ^ 3
        = (C4 + 252) * ‖Work.Kernels.qParamFun z‖ ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right hC4' hq3
  · rw [hscale, mul_one]
    calc ‖Work.Kernels.jInvariantFun z * Work.Kernels.qParamFun z - 1
          - 744 * Work.Kernels.qParamFun z
          - 196884 * (Work.Kernels.qParamFun z) ^ 2‖
          ≤ C5 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h5 z hz
      _ ≤ (C1 + C2 + C3 + (C4 + 252) + C5 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_right hC5' hq3

end Work.Asymptotics
