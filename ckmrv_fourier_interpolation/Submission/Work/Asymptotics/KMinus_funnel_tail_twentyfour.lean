/-
# Funnel tail expansion of `K₋^{(24)}`

This file proves `Work.Asymptotics.KMinus_funnel_tail_twentyfour`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelMainBoundDecay2

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## Assembly of the target -/

/-- The inverse of `Sh` is bounded by `16` on the region. -/
theorem funnel_Sh_inv_le (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖(Compact.Sh τ z)⁻¹‖ ≤ 16 := by
  have h : (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := funnel_Sh_ge τ z t hτ ht hz
  have hpos : 0 < ‖Compact.Sh τ z‖ := lt_of_lt_of_le (by norm_num) h
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  linarith

/-- The target from the core (decaying) bracket bound. -/
theorem KMinus_funnel_tail_twentyfour_of_main (ℓ : Work.Kernels.LogLambdaData)
    (hmain : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im)))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨Cb, Nb, Mb, hCb, hNb, hMb, hbound⟩ := hmain
  refine ⟨(3456 * Real.pi)⁻¹ * 16 * Cb, Nb, Mb, by positivity, hNb, hMb, ?_⟩
  intro τ z t hτ ht hz
  have hSh : (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := funnel_Sh_ge τ z t hτ ht hz
  have hShne : Compact.Sh τ z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hSh
    norm_num at hSh
  have hinv : ‖(Compact.Sh τ z)⁻¹‖ ≤ 16 := funnel_Sh_inv_le τ z t hτ ht hz
  have htail := Compact.tail_identity ℓ 24 (Or.inr rfl) τ z hShne
  have hnorm : (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖
      = ‖(Compact.Sh τ z)⁻¹ * (Compact.brMinus ℓ 24 τ z
          + Compact.Sh τ z * Compact.br0 24 ℓ τ z)‖ := by
    have h2 : ‖(3456 : ℂ) * (Real.pi : ℂ)
        * (Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z)‖
        = (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 24 τ z
            - Compact.Gminus 24 ℓ τ z‖ := by
      rw [norm_mul, norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [← h2, htail, norm_neg]
  have hb := hbound τ z t hτ ht hz
  have hkey : (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖
      ≤ 16 * (Cb * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb
          * Real.exp (-(Real.pi * (t - τ.im)))) := by
    rw [hnorm]
    calc ‖(Compact.Sh τ z)⁻¹ * (Compact.brMinus ℓ 24 τ z
          + Compact.Sh τ z * Compact.br0 24 ℓ τ z)‖
        ≤ ‖(Compact.Sh τ z)⁻¹‖ * ‖Compact.brMinus ℓ 24 τ z
            + Compact.Sh τ z * Compact.br0 24 ℓ τ z‖ := norm_mul_le _ _
      _ ≤ 16 * (Cb * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb
            * Real.exp (-(Real.pi * (t - τ.im)))) :=
          mul_le_mul hinv hb (norm_nonneg _) (by norm_num)
  have hstep : ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖
      ≤ (3456 * Real.pi)⁻¹ * (16 * (Cb * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb
          * Real.exp (-(Real.pi * (t - τ.im))))) := by
    calc ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖
        = (3456 * Real.pi)⁻¹ * ((3456 * Real.pi)
            * ‖Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (3456 * Real.pi) ≠ 0), one_mul]
      _ ≤ (3456 * Real.pi)⁻¹ * (16 * (Cb * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb
            * Real.exp (-(Real.pi * (t - τ.im))))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  ring


/-- **Funnel tail expansion of `K₋^{(24)}`.**

For `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t`, `t ≥ Im τ + 1`, the kernel
`K₋^{(24)}` differs from `Compact.Gminus 24` by `O((scale τ)^N (1+t)^M e^{-π(t - Im τ)})`. -/
theorem KMinus_funnel_tail_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KMinus ℓ 24 τ z - Work.Asymptotics.Compact.Gminus 24 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) :=
  KMinus_funnel_tail_twentyfour_of_main ℓ (KMinusFunnelMainBoundDecay2 ℓ)

end
end Work.Asymptotics
