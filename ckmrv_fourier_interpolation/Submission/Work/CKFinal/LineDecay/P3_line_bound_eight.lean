import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_pointwise_majorant_eight
import Submission.Work.CKFinal.LineDecay.Tail_integral_eight

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane
open scoped Topology

/-- **The tail piece `P₃` is exponentially small on the two lines, uniformly in `r`** (dimension 8,
for both kernels).

`P₃(K) r τ = ∫_{t ≥ 1} Φ(K)(τ,t)·gaussWeight r t dt` and `‖gaussWeight r t‖ = e^{-πr²t} ≤ 1`, so
`‖P₃‖ ≤ ∫_{t ≥ 1} ‖Φ(τ,t)‖ dt` once the (weighted) integrand is known to be integrable;
`Phi_tail_bound_eight` gives exactly `∫_{t ≥ 1} ‖Φ(τ,t)‖ dt ≤ C·Im τ^N·e^{-π Im τ}` and the
pointwise input is `Phi_axis_eq` together with `KPlus_tail_lines`/`KMinus_tail_lines`
(`‖Φ(τ,t)‖ ≤ B·(1+t)^A·e^{-πt}/(1+e^{2π(Im τ - t)})`, hence summable by `Tail_integral_eight`).
The two kernels are `Kfun` and `Khat`. -/
theorem P3_line_bound_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P3 (Work.Kernels.Khat ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))) := by
  obtain ⟨C, A, Y, hC0, hA0, hY1, hmaj⟩ := Phi_pointwise_majorant_eight ℓ
  obtain ⟨CI, hCI, hI⟩ := Tail_integral_eight A
  refine ⟨C * CI * 2 ^ (3 * A) + 1, 2 * A, max Y 1, ?_, ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (2 : ℝ) ^ (3 * A) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 ≤ C * CI * (2 : ℝ) ^ (3 * A) := mul_nonneg (mul_nonneg hC0 hCI.le) h1.le
    linarith
  · linarith
  · exact le_max_right Y 1
  · intro τ r hre hY
    have hYτ : Y ≤ τ.im := le_trans (le_max_left Y 1) hY
    have hy1 : (1 : ℝ) ≤ τ.im := le_trans (le_max_right Y 1) hY
    have hy0 : (0 : ℝ) < τ.im := lt_of_lt_of_le one_pos hy1
    obtain ⟨hIint, hIval⟩ := hI τ.im hy1
    -- `1 + ‖τ‖ ≤ 2 (1 + Im τ)` on the two lines.
    have hτn_le : 1 + ‖(τ : ℂ)‖ ≤ 2 * (1 + τ.im) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos hy0] at h1
      have h2 : |τ.re| = 1 / 2 := by rcases hre with h | h <;> rw [h] <;> norm_num
      rw [h2] at h1
      linarith
    have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
    -- `(1+‖τ‖)^A (1+Im τ)^A ≤ 2^{3A} (Im τ)^{2A}`.
    have hsc : (1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ A ≤ (2 : ℝ) ^ (3 * A) * τ.im ^ (2 * A) := by
      have h2 : (1 + ‖(τ : ℂ)‖) ^ A ≤ ((2 : ℝ) * (1 + τ.im)) ^ A :=
        Real.rpow_le_rpow hs0 hτn_le hA0
      have h3 : ((2 : ℝ) * (1 + τ.im)) ^ A = (2 : ℝ) ^ A * (1 + τ.im) ^ A :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h4 : (1 + τ.im) ^ A * (1 + τ.im) ^ A = (1 + τ.im) ^ (2 * A) := by
        rw [← Real.rpow_add (by linarith)]; congr 1; ring
      have h5 : (1 + τ.im) ^ (2 * A) ≤ ((2 : ℝ) * τ.im) ^ (2 * A) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by nlinarith)
      have h6 : ((2 : ℝ) * τ.im) ^ (2 * A) = (2 : ℝ) ^ (2 * A) * τ.im ^ (2 * A) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h7 : (2 : ℝ) ^ A * (2 : ℝ) ^ (2 * A) = (2 : ℝ) ^ (3 * A) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      calc (1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ A
          ≤ ((2 : ℝ) ^ A * (1 + τ.im) ^ A) * (1 + τ.im) ^ A :=
            mul_le_mul_of_nonneg_right (le_trans h2 (le_of_eq h3))
              (Real.rpow_nonneg (by linarith) _)
        _ = (2 : ℝ) ^ A * ((1 + τ.im) ^ A * (1 + τ.im) ^ A) := by ring
        _ = (2 : ℝ) ^ A * (1 + τ.im) ^ (2 * A) := by rw [h4]
        _ ≤ (2 : ℝ) ^ A * ((2 : ℝ) ^ (2 * A) * τ.im ^ (2 * A)) :=
            mul_le_mul_of_nonneg_left (le_trans h5 (le_of_eq h6))
              (Real.rpow_nonneg (by norm_num) _)
        _ = ((2 : ℝ) ^ A * (2 : ℝ) ^ (2 * A)) * τ.im ^ (2 * A) := by ring
        _ = (2 : ℝ) ^ (3 * A) * τ.im ^ (2 * A) := by rw [h7]
    -- The reduction `‖P₃(K)‖ ≤ C (1+‖τ‖)^A · ∫_{t≥1} (1+t)^A e^{-πt}/(1+e^{2π(Im τ-t)})`.
    have key : ∀ K : ℍ → ℍ → ℂ,
        (∀ t, 1 ≤ t → ‖Work.CKFinal.Phi K τ t‖ ≤
            C * (1 + ‖(τ : ℂ)‖) ^ A * ((1 + t) ^ A *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))) →
        ‖Work.CKFinal.P3 K r τ‖ ≤
          (C * CI * (2 : ℝ) ^ (3 * A) + 1) * τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im)) := by
      intro K hK
      have hB0 : 0 ≤ C * (1 + ‖(τ : ℂ)‖) ^ A := mul_nonneg hC0 (Real.rpow_nonneg hs0 A)
      have hle : ∀ t, 1 ≤ t → ‖Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ ≤
          (C * (1 + ‖(τ : ℂ)‖) ^ A) * ((1 + t) ^ A *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
        intro t ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
        have hE0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * t))
            / (1 + Real.exp (2 * Real.pi * (τ.im - t))) := by positivity
        have hX0 : (0 : ℝ) ≤ (1 + t) ^ A * (Real.exp (-(Real.pi * t))
            / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
          mul_nonneg (Real.rpow_nonneg (by linarith) A) hE0
        have hgw : ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
          rw [Work.Asymptotics.norm_gaussWeight, Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ Real.pi * r ^ 2 * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
          linarith
        rw [norm_mul]
        calc ‖Work.CKFinal.Phi K τ t‖ * ‖Work.Asymptotics.gaussWeight r t‖
            ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A * ((1 + t) ^ A * (Real.exp (-(Real.pi * t))
                / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))) * 1 :=
              mul_le_mul (hK t ht) hgw (norm_nonneg _) (mul_nonneg hB0 hX0)
          _ = (C * (1 + ‖(τ : ℂ)‖) ^ A) * ((1 + t) ^ A * (Real.exp (-(Real.pi * t))
                / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by ring
      have hint : MeasureTheory.Integrable (fun t => (C * (1 + ‖(τ : ℂ)‖) ^ A) * ((1 + t) ^ A *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))))
          (MeasureTheory.volume.restrict (Set.Ici 1)) := hIint.const_mul _
      calc ‖Work.CKFinal.P3 K r τ‖
          = ‖∫ t in Set.Ici 1, Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ := by
            rw [Work.CKFinal.P3, Work.CKFinal.hsplit]
        _ ≤ ∫ t in Set.Ici 1, ‖Work.CKFinal.Phi K τ t * Work.Asymptotics.gaussWeight r t‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ t in Set.Ici 1, (C * (1 + ‖(τ : ℂ)‖) ^ A) * ((1 + t) ^ A *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
            exact hle t ht
        _ = (C * (1 + ‖(τ : ℂ)‖) ^ A) * ∫ t in Set.Ici 1, ((1 + t) ^ A *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A) * (CI * (1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im))) :=
            mul_le_mul_of_nonneg_left hIval hB0
        _ ≤ (C * CI * (2 : ℝ) ^ (3 * A) + 1) * τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im)) := by
            have he0 : 0 ≤ Real.exp (-(Real.pi * τ.im)) := (Real.exp_pos _).le
            have hyA0 : 0 ≤ τ.im ^ (2 * A) := Real.rpow_nonneg hy0.le _
            have hstep : (1 + ‖(τ : ℂ)‖) ^ A * ((1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))
                ≤ (2 : ℝ) ^ (3 * A) * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := by
              have h := mul_le_mul_of_nonneg_right hsc he0
              calc (1 + ‖(τ : ℂ)‖) ^ A * ((1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))
                  = ((1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ A)
                      * Real.exp (-(Real.pi * τ.im)) := by ring
                _ ≤ ((2 : ℝ) ^ (3 * A) * τ.im ^ (2 * A))
                      * Real.exp (-(Real.pi * τ.im)) := h
                _ = (2 : ℝ) ^ (3 * A) * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := by ring
            have hmid : C * (1 + ‖(τ : ℂ)‖) ^ A
                  * (CI * (1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))
                ≤ C * CI * (2 : ℝ) ^ (3 * A)
                    * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := by
              calc C * (1 + ‖(τ : ℂ)‖) ^ A * (CI * (1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))
                  = (C * CI) * ((1 + ‖(τ : ℂ)‖) ^ A
                      * ((1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))) := by ring
                _ ≤ (C * CI) * ((2 : ℝ) ^ (3 * A)
                      * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im)))) :=
                    mul_le_mul_of_nonneg_left hstep (by positivity)
                _ = C * CI * (2 : ℝ) ^ (3 * A)
                      * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := by ring
            have hfin : C * CI * (2 : ℝ) ^ (3 * A) * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im)))
                ≤ (C * CI * (2 : ℝ) ^ (3 * A) + 1)
                    * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := by
              have h0 : 0 ≤ τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im)) := mul_nonneg hyA0 he0
              exact mul_le_mul_of_nonneg_right (by linarith) h0
            calc C * (1 + ‖(τ : ℂ)‖) ^ A * (CI * (1 + τ.im) ^ A * Real.exp (-(Real.pi * τ.im)))
                ≤ C * CI * (2 : ℝ) ^ (3 * A)
                    * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := hmid
              _ ≤ (C * CI * (2 : ℝ) ^ (3 * A) + 1)
                    * (τ.im ^ (2 * A) * Real.exp (-(Real.pi * τ.im))) := hfin
              _ = (C * CI * (2 : ℝ) ^ (3 * A) + 1) * τ.im ^ (2 * A)
                    * Real.exp (-(Real.pi * τ.im)) := by ring
    exact ⟨key (Work.Kernels.Kfun ℓ 8) (fun t ht => (hmaj τ t hre hYτ ht).1),
           key (Work.Kernels.Khat ℓ 8) (fun t ht => (hmaj τ t hre hYτ ht).2)⟩

end Work.CKFinal.LineDecay
