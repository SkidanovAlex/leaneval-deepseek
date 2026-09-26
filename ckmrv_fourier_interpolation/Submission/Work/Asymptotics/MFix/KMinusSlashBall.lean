import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.All
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.ThetaAux
import Submission.Work.Rigidity.bounded_on_lt_im_of_periodic
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.cuspAtomLimits
import Submission.Work.Asymptotics.MFix.KMinusCuspBall
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.MFix.MdiffEta

namespace Work.Asymptotics.MFix

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

/-- **Assembly step.**  Given (i) the uniform crude bound on `Ncusp`, (ii) the vanishing of the
cusp limit of `η = E·Ncusp` and (iii) the holomorphy of `η`, the target estimate follows by the
Schwarz-lemma argument `periodic_zero_cusp_decay_uhp` together with the identification
`Ncusp_ident`. -/
theorem slash_cusp_ball_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      ‖Ncusp ℓ d τ z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hlim : ∀ τ : UpperHalfPlane, Filter.Tendsto (fun z : UpperHalfPlane => Ecusp z * Ncusp ℓ d τ z)
      atImInfty (𝓝 0))
    (hmdiff : ∀ τ : UpperHalfPlane, DifferentiableOn ℂ
      (fun w : ℂ => Ecusp (UpperHalfPlane.ofComplex w) * Ncusp ℓ d τ (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨B, hB0, hB⟩ := hbound
  refine ⟨B * Real.exp (2 * Real.pi) + 1, by positivity, fun τ z hτ hz hne => ?_⟩
  -- Step 1: the sharp decay of `Ncusp`
  have hdec : ‖Ncusp ℓ d τ z‖ ≤ (B * Real.exp (2 * Real.pi)) * Real.exp (-(Real.pi * z.im)) := by
    set g : ℍ → ℂ := fun w => Ecusp w * Ncusp ℓ d τ w with hg
    have hperp : ∀ w : ℍ, g ((1 : ℝ) +ᵥ w) = g w := by
      intro w; simp only [hg, Ecusp_vadd_one, Ncusp_vadd_one]
      ring
    have hmd : MDiff g := by
      rw [hg]; exact (UpperHalfPlane.mdifferentiable_iff).mpr (hmdiff τ)
    have hBg : ∀ w : ℍ, 1 ≤ w.im → ‖g w‖ ≤ B := by
      intro w hw
      rw [hg, norm_mul, norm_Ecusp]
      calc Real.exp (-(Real.pi * w.im)) * ‖Ncusp ℓ d τ w‖
          ≤ Real.exp (-(Real.pi * w.im)) * (B * Real.exp (Real.pi * w.im)) :=
            mul_le_mul_of_nonneg_left (hB τ w hτ hw) (Real.exp_nonneg _)
        _ = B := by
            rw [show Real.exp (-(Real.pi * w.im)) * (B * Real.exp (Real.pi * w.im))
                = (Real.exp (-(Real.pi * w.im)) * Real.exp (Real.pi * w.im)) * B by ring,
              ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have h := periodic_zero_cusp_decay_uhp hB0.le hperp hmd hBg (hlim τ) z hz
    rw [hg, norm_mul, norm_Ecusp] at h
    have h1 : ‖Ncusp ℓ d τ z‖ ≤ Real.exp (Real.pi * z.im) *
        (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) := by
      calc ‖Ncusp ℓ d τ z‖
          = Real.exp (Real.pi * z.im) * (Real.exp (-(Real.pi * z.im)) * ‖Ncusp ℓ d τ z‖) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (Real.pi * z.im) *
              (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) :=
            mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    calc ‖Ncusp ℓ d τ z‖
        ≤ Real.exp (Real.pi * z.im) *
            (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) := h1
      _ = (B * Real.exp (2 * Real.pi)) * Real.exp (-(Real.pi * z.im)) := by
          rw [show Real.exp (Real.pi * z.im) * (B * Real.exp (2 * Real.pi) *
                Real.exp (-(2 * Real.pi * z.im)))
              = B * Real.exp (2 * Real.pi) *
                (Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im))) by ring,
            ← Real.exp_add,
            show Real.pi * z.im + -(2 * Real.pi * z.im) = -(Real.pi * z.im) by ring]
  -- Step 2: identify the two sides
  have hD : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : (z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)
      = Ncusp ℓ d τ z /
        (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
    rw [Ncusp_ident ℓ d hd τ z hne, mul_div_cancel_left₀ _ hD]
  rw [hkey, norm_div]
  refine le_trans (div_le_div_of_nonneg_right ?_ (norm_nonneg _)) (le_refl _)
  have hX : (0 : ℝ) ≤ B * Real.exp (2 * Real.pi) := mul_nonneg hB0.le (Real.exp_pos _).le
  have hY : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) := by
    have := norm_nonneg (z : ℂ); nlinarith
  have hE : (0 : ℝ) < Real.exp (-(Real.pi * z.im)) := Real.exp_pos _
  calc ‖Ncusp ℓ d τ z‖ ≤ (B * Real.exp (2 * Real.pi)) * Real.exp (-(Real.pi * z.im)) := hdec
    _ ≤ (B * Real.exp (2 * Real.pi)) * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im)) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hX) hE.le
        simpa using h
    _ ≤ (B * Real.exp (2 * Real.pi) + 1) * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

theorem KMinus_slash_cusp_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
  slash_cusp_ball_of ℓ d hd hR (KMinusCuspBallBound ℓ d hd hR) (KMinusCuspBallLimit ℓ d hd)
    (mdiff_eta ℓ d)

end Work.Asymptotics.MFix
