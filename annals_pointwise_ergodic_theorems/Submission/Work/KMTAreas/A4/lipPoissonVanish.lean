import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The dilation of a Schwartz function: `t ↦ ε * ψ (ε * t)` is again Schwartz. -/
lemma exists_smul_dilate (ψ : SchwartzR) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : SchwartzR, (H : ℝ → ℂ) = fun t : ℝ => (ε : ℂ) * (ψ : ℝ → ℂ) (ε * t) := by
  have hg : Function.HasTemperateGrowth (fun t : ℝ => ε * t) := by fun_prop
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun _ : ℝ => (ε : ℂ))
      (SchwartzMap.compCLM ℂ hg ⟨1, ε⁻¹, ?_⟩ ψ), ?_⟩
  · intro x
    rw [pow_one]
    have h1 : ‖(fun t : ℝ => ε * t) x‖ = ε * ‖x‖ := by
      rw [norm_mul, Real.norm_of_nonneg hε.le]
    rw [h1]
    have h3 : ε⁻¹ * (1 + ε * ‖x‖) = ε⁻¹ + ‖x‖ := by
      rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    rw [h3]
    linarith [inv_pos.mpr hε]
  · funext t
    simp [SchwartzMap.compCLM_apply]

/-- Poisson summation in the "sampled lattice" form: for a Schwartz function `ψ` with Fourier
transform `ψ̂`, `ε ∑_{u ∈ ℤ} ψ(εu) e(-uθ) = ∑_{n ∈ ℤ} ψ̂((θ+n)/ε)`. -/
lemma poissonSampledLattice (ψ : SchwartzR) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    (ε : ℂ) * ∑' u : ℤ, ((ψ (ε * (u : ℝ)) : ℂ) *
        (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ))
      = ∑' n : ℤ, schFT ψ ((θ + (n : ℝ)) / ε) := by
  obtain ⟨H, hH⟩ := exists_smul_dilate ψ hε
  have hFT : ∀ ξ : ℝ, (𝓕 H) ξ = (𝓕 ψ) (ξ / ε) := by
    intro ξ
    rw [SchwartzMap.fourier_coe, hH]
    exact realFourier_dilation (ψ : ℝ → ℂ) hε ξ
  have hinv : ∀ y : ℝ, (𝓕 (𝓕 H)) y = (H : ℝ → ℂ) (-y) := by
    intro y
    have h2 : 𝓕⁻ ((𝓕 H : SchwartzR) : ℝ → ℂ) = (H : ℝ → ℂ) := by
      have hint2 : Integrable (𝓕 ((H : ℝ → ℂ))) := by
        rw [← SchwartzMap.fourier_coe H]
        exact (𝓕 H).integrable
      have hcont := Continuous.fourierInv_fourier_eq (f := (H : ℝ → ℂ))
        H.continuous H.integrable hint2
      rwa [← SchwartzMap.fourier_coe H] at hcont
    have h1 : (𝓕 ((𝓕 H : SchwartzR) : ℝ → ℂ)) y
        = 𝓕⁻ ((𝓕 H : SchwartzR) : ℝ → ℂ) (-y) := by
      rw [Real.fourierInv_eq_fourier_neg ((𝓕 H : SchwartzR) : ℝ → ℂ) (-y), neg_neg]
    rw [SchwartzMap.fourier_coe, h1, h2]
  have hpois := SchwartzMap.tsum_eq_tsum_fourier (𝓕 H) θ
  have hleft : (∑' n : ℤ, (𝓕 H) (θ + (n : ℝ)))
      = ∑' n : ℤ, schFT ψ ((θ + (n : ℝ)) / ε) := by
    refine tsum_congr fun n => ?_
    rw [hFT]
    rfl
  have hright : (∑' n : ℤ, (𝓕 (𝓕 H)) (n : ℝ) *
        (fourier n ((θ : ℝ) : UnitAddCircle) : ℂ))
      = ∑' u : ℤ, ((ε : ℂ) * ((ψ (ε * (u : ℝ)) : ℂ) *
          (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ))) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun u : ℤ => ((ε : ℂ) * ((ψ (ε * (u : ℝ)) : ℂ) *
          (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ))))]
    refine tsum_congr fun n => ?_
    rw [hinv, hH]
    simp only [Equiv.neg_apply, Int.cast_neg, neg_neg]
    ring
  rw [← tsum_mul_left]
  exact hright.symm.trans (hpois.symm.trans hleft)

theorem lipPoissonVanish (ψ : Work.Analysis.InverseTheory.SchwartzR)
    (hη : ∀ s : ℝ, 1 < |s| → Work.KMTAreas.A4.schFT ψ s = 0)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : ∀ n : ℤ, ε < |θ - n|) :
    (ε : ℂ) * ∑' u : ℤ, ((ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((θ : ℝ) : Work.Analysis.InverseTheory.FreqCircle) : ℂ))
      = 0 := by
  rw [poissonSampledLattice ψ hε θ]
  have h0 : ∀ n : ℤ, schFT ψ ((θ + (n : ℝ)) / ε) = 0 := by
    intro n
    apply hη
    rw [abs_div, abs_of_pos hε, lt_div_iff₀ hε]
    have h := hθ (-n)
    simp only [Int.cast_neg, sub_neg_eq_add] at h
    simpa using h
  rw [tsum_congr h0, tsum_zero]

end Work.KMTAreas.A4
