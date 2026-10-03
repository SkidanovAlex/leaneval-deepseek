import Mathlib
import Submission.Work.KMTAreas.A4.offKernelId

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped FourierTransform BigOperators

namespace Work.KMTAreas.A4

/-- The Fourier transform of a translate of a function on `ℝ`: translating the argument by `c`
multiplies the Fourier transform by the unimodular factor `e(-c·w)`. -/
lemma fourier_comp_sub (F : ℝ → ℂ) (c : ℝ) (w : ℝ) :
    𝓕 (fun y : ℝ => F (y - c)) w = Real.fourierChar (-(c * w)) • 𝓕 F w := by
  have h := VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar)
      (μ := volume) (L := innerₗ ℝ) (f := F) (v₀ := -c)
  have hw := congrFun h w
  have hL : (innerₗ ℝ (-c)) w = -(c * w) := by simp; ring
  rw [hL] at hw
  exact hw

/-- Translating the argument of a function does not change the modulus of its Fourier transform. -/
lemma norm_fourier_comp_sub (F : ℝ → ℂ) (c : ℝ) (w : ℝ) :
    ‖𝓕 (fun y : ℝ => F (y - c)) w‖ = ‖𝓕 F w‖ := by
  rw [fourier_comp_sub, Circle.norm_smul]

/-- The Fourier transform of a finite sum of translates is the sum of the Fourier transforms. -/
lemma fourier_finsetSum_sub {ι : Type*} (A : Finset ι) (c : ι → ℝ) (F : ℝ → ℂ)
    (hint : Integrable F) (w : ℝ) :
    𝓕 (fun y : ℝ => ∑ α ∈ A, F (y - c α)) w
      = ∑ α ∈ A, 𝓕 (fun y : ℝ => F (y - c α)) w := by
  have hf : ∀ α ∈ A, Integrable (fun v : ℝ => Real.fourierChar (-inner ℝ v w) • F (v - c α)) := by
    intro α _
    rw [Real.fourierIntegral_convergent_iff (μ := volume) w]
    exact hint.comp_sub_right (c α)
  rw [Real.fourier_eq]
  simp only [Real.fourier_eq]
  rw [← integral_finsetSum A (f := fun α v => Real.fourierChar (-inner ℝ v w) • F (v - c α)) hf]
  congr 1 with v
  simp only [Circle.smul_def, smul_eq_mul, Finset.mul_sum]

/-- The Fourier transform of a sum of `#A` translates is bounded by `#A` times the modulus of the
Fourier transform of the original function. -/
lemma norm_fourier_sub_sum_le {ι : Type*} (A : Finset ι) (c : ι → ℝ) (F : ℝ → ℂ)
    (hint : Integrable F) (w : ℝ) :
    ‖𝓕 (fun y : ℝ => ∑ α ∈ A, F (y - c α)) w‖ ≤ (A.card : ℝ) * ‖𝓕 F w‖ := by
  rw [fourier_finsetSum_sub A c F hint w]
  calc ‖∑ α ∈ A, 𝓕 (fun y : ℝ => F (y - c α)) w‖
      ≤ ∑ α ∈ A, ‖𝓕 (fun y : ℝ => F (y - c α)) w‖ := norm_sum_le A _
    _ = ∑ _α ∈ A, ‖𝓕 F w‖ :=
        Finset.sum_congr rfl (fun α _ => norm_fourier_comp_sub F (c α) w)
    _ = (A.card : ℝ) * ‖𝓕 F w‖ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem offKernNormLe (ρ : ℝ) (l : ℕ) (Φ : SchwartzMap ℝ ℂ) (j : ℤ) :
    ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))) j‖
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) *
          ‖FourierTransform.fourier (Φ : ℝ → ℂ) (j : ℝ)‖ := by
  rw [offKernelId ρ l Φ j]
  exact norm_fourier_sub_sum_le (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val) (Φ : ℝ → ℂ)
    (Φ.integrable : Integrable (Φ : ℝ → ℂ)) (j : ℝ)

end Work.KMTAreas.A4
