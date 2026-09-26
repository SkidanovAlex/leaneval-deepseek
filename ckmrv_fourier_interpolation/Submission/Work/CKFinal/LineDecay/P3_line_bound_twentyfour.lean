import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_tail_bound_twentyfour
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.Phi_pointwise_cusp_bound_twentyfour

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane

noncomputable section

/-- **The tail piece `P₃` is exponentially small on the two lines, uniformly in `r`** (dimension 24,
rate `e^{-3π Im τ}`, for both kernels).  `P₃(K) r τ = ∫_{t ≥ 1} Φ(K)(τ,t)·gaussWeight r t dt` and
`‖gaussWeight r t‖ = e^{-πr²t} ≤ 1`, so `‖P₃‖ ≤ ∫_{t ≥ 1}‖Φ(τ,t)‖ dt`; the pointwise
`Φ`-estimates of dimension 24 are supplied by `Phi_axis_norm_twentyfour` together with
`KPlus_tail_lines_twentyfour`/`KMinus_tail_lines_twentyfour`, and the majorant is summable. -/
theorem P3_line_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P3 (Work.Kernels.Khat ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) := by
  -- The pointwise cusp majorant for `Φ`, for both kernels, on the two lines.
  obtain ⟨Cp, Ap, Yp, hCp, hAp, hYp, hpw⟩ := Phi_pointwise_cusp_bound_twentyfour ℓ
  -- The elementary tail integral: `∫_{t ≥ 1} e^{-2πy} e^{-πt}/(1+e^{2π(y-t)}) dt ≤ CI e^{-3πy}`.
  obtain ⟨CI, hCI, hI⟩ := Tail_integral_twentyfour
  have hC0 : 0 ≤ Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1 := by
    have h := mul_nonneg (mul_nonneg hCp hCI.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * Ap))
    linarith
  refine ⟨Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1, Ap, Yp, hC0, hAp, hYp, ?_⟩
  intro τ r hre hYτ
  have hy1 : 1 ≤ τ.im := le_trans hYp hYτ
  have hy0 : 0 < τ.im := by linarith
  -- `1 + ‖τ‖ ≤ 2(1 + Im τ) ≤ 4 Im τ`, hence `(1+‖τ‖)^Ap ≤ 2^{2Ap} (Im τ)^Ap`.
  have hτn_le : 1 + ‖(τ : ℂ)‖ ≤ 2 * (1 + τ.im) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos hy0] at h1
    have h2 : |τ.re| = 1 / 2 := by rcases hre with h | h <;> rw [h] <;> norm_num
    rw [h2] at h1
    linarith
  have hXA : (1 + ‖(τ : ℂ)‖) ^ Ap ≤ (2 : ℝ) ^ (2 * Ap) * τ.im ^ Ap := by
    have h2 : (1 + ‖(τ : ℂ)‖) ^ Ap ≤ (2 * (1 + τ.im)) ^ Ap :=
      Real.rpow_le_rpow (by positivity) hτn_le hAp
    have h3 : (2 * (1 + τ.im)) ^ Ap = (2 : ℝ) ^ Ap * (1 + τ.im) ^ Ap :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h4 : (1 + τ.im) ^ Ap ≤ (2 * τ.im) ^ Ap :=
      Real.rpow_le_rpow (by linarith) (by linarith) hAp
    have h5 : (2 * τ.im) ^ Ap = (2 : ℝ) ^ Ap * τ.im ^ Ap :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h6 : (2 : ℝ) ^ Ap * (2 : ℝ) ^ Ap = (2 : ℝ) ^ (2 * Ap) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    calc (1 + ‖(τ : ℂ)‖) ^ Ap ≤ (2 * (1 + τ.im)) ^ Ap := h2
      _ = (2 : ℝ) ^ Ap * (1 + τ.im) ^ Ap := h3
      _ ≤ (2 : ℝ) ^ Ap * ((2 : ℝ) ^ Ap * τ.im ^ Ap) :=
          mul_le_mul_of_nonneg_left (le_trans h4 (le_of_eq h5))
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) Ap)
      _ = (2 : ℝ) ^ (2 * Ap) * τ.im ^ Ap := by rw [← mul_assoc, h6]
  -- The common majorant `B · Ecusp` on `t ≥ 1`, with `B = Cp (1+‖τ‖)^Ap`.
  set B : ℝ := Cp * (1 + ‖(τ : ℂ)‖) ^ Ap with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set Ecusp : ℝ → ℝ := fun t => Real.exp (-(2 * Real.pi * τ.im)) *
    (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) with hEdef
  have hEint : Integrable Ecusp (volume.restrict (Set.Ici (1 : ℝ))) := by
    have h := (hI τ.im hy1).1
    rw [hEdef]
    exact h
  have hEval : ∫ t in Set.Ici (1 : ℝ), Ecusp t ≤ CI * Real.exp (-(3 * Real.pi * τ.im)) := by
    rw [hEdef]
    exact (hI τ.im hy1).2
  have hgint : Integrable (fun t => B * Ecusp t) (volume.restrict (Set.Ici (1 : ℝ))) :=
    hEint.const_mul B
  -- The polynomial comparison `B · CI · e^{-3πy} ≤ C · y^Ap · e^{-3πy}`.
  have arith : B * (CI * Real.exp (-(3 * Real.pi * τ.im))) ≤
      (Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1) * τ.im ^ Ap *
        Real.exp (-(3 * Real.pi * τ.im)) := by
    have hyA0 : 0 ≤ τ.im ^ Ap := Real.rpow_nonneg (by linarith) Ap
    have he0 : 0 ≤ Real.exp (-(3 * Real.pi * τ.im)) := (Real.exp_pos _).le
    have hXe : (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(3 * Real.pi * τ.im))
        ≤ ((2 : ℝ) ^ (2 * Ap) * τ.im ^ Ap) * Real.exp (-(3 * Real.pi * τ.im)) :=
      mul_le_mul_of_nonneg_right hXA he0
    have hk0 : 0 ≤ Cp * CI := mul_nonneg hCp hCI.le
    calc B * (CI * Real.exp (-(3 * Real.pi * τ.im)))
        = (Cp * CI) * ((1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(3 * Real.pi * τ.im))) := by
          rw [hBdef]; ring
      _ ≤ (Cp * CI) * (((2 : ℝ) ^ (2 * Ap) * τ.im ^ Ap) *
            Real.exp (-(3 * Real.pi * τ.im))) := mul_le_mul_of_nonneg_left hXe hk0
      _ = (Cp * CI * (2 : ℝ) ^ (2 * Ap)) *
            (τ.im ^ Ap * Real.exp (-(3 * Real.pi * τ.im))) := by ring
      _ ≤ (Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1) *
            (τ.im ^ Ap * Real.exp (-(3 * Real.pi * τ.im))) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hyA0 he0)
      _ = (Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1) * τ.im ^ Ap *
            Real.exp (-(3 * Real.pi * τ.im)) := by ring
  -- `‖P₃‖ ≤ ∫_{t ≥ 1} B · Ecusp`.
  have key : ∀ (K : UpperHalfPlane → UpperHalfPlane → ℂ),
      (∀ (s : ℝ), 1 ≤ s → ‖Work.CKFinal.Phi K τ s‖ ≤ B * Ecusp s) →
      ‖∫ t in Set.Ici (1 : ℝ), Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ ≤
        (Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1) * τ.im ^ Ap *
          Real.exp (-(3 * Real.pi * τ.im)) := by
    intro K hK
    have hle : ∀ t : ℝ, 1 ≤ t →
        ‖Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ ≤ B * Ecusp t := by
      intro t ht1
      have ht0 : 0 < t := by linarith
      have hgw : ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
        rw [Work.Asymptotics.norm_gaussWeight]
        refine Real.exp_le_one_iff.mpr ?_
        have h1 : 0 ≤ Real.pi * r ^ 2 * t :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
        linarith
      have hEp0 : 0 ≤ Ecusp t := by rw [hEdef]; positivity
      calc ‖Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖
          = ‖Work.CKFinal.Phi K τ t‖ * ‖Work.Asymptotics.gaussWeight r t‖ := norm_mul _ _
        _ ≤ (B * Ecusp t) * 1 :=
            mul_le_mul (hK t ht1) hgw (norm_nonneg _) (mul_nonneg hB0 hEp0)
        _ = B * Ecusp t := by ring
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ ≤ B * Ecusp t := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
      exact hle t ht
    have hInt := MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ici (1 : ℝ)))
      hgint hae
    calc ‖∫ t in Set.Ici (1 : ℝ), Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖
        ≤ ∫ t in Set.Ici (1 : ℝ), B * Ecusp t := hInt
      _ = B * ∫ t in Set.Ici (1 : ℝ), Ecusp t := MeasureTheory.integral_const_mul B Ecusp
      _ ≤ B * (CI * Real.exp (-(3 * Real.pi * τ.im))) := mul_le_mul_of_nonneg_left hEval hB0
      _ ≤ (Cp * CI * (2 : ℝ) ^ (2 * Ap) + 1) * τ.im ^ Ap *
            Real.exp (-(3 * Real.pi * τ.im)) := arith
  constructor
  · rw [Work.CKFinal.P3, Work.CKFinal.hsplit]
    exact key (Work.Kernels.Kfun ℓ 24)
      (fun s hs => by rw [hEdef]; exact (hpw τ s (by linarith) hre hYτ hs).1)
  · rw [Work.CKFinal.P3, Work.CKFinal.hsplit]
    exact key (Work.Kernels.Khat ℓ 24)
      (fun s hs => by rw [hEdef]; exact (hpw τ s (by linarith) hre hYτ hs).2)

end

end Work.CKFinal.LineDecay
