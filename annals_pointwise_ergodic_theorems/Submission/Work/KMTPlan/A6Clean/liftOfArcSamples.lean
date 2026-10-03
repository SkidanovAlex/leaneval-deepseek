import Mathlib
import Submission.Work.KMTAreas.A7Rep.envAux
import Submission.Work.KMTPlan.A6Clean.liftMemLpTwo
import Submission.Work.KMTPlan.A6Clean.fourierInvCompNeg
import Submission.Work.BourgainPlan.IonescuWainger.discFourier_mul_eq_circConv_l1
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate
import Submission.Work.KMTAreas.A4.fourierZCoeFnEqTsum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The samples of an `L²`-band-limited function.**  If `g : ℤ → ℂ` is square summable with
`ftLp g` supported in the arc `arcSet 0 γ` around `0` (`γ < 1/2`), then `g` is the restriction to
`ℤ` of `𝓕⁻ A` for an `L²` function `A : ℝ → ℂ` supported in the interval `Icc (-γ) γ`.

The amplitude is the *reflected* realization of the (pointwise-supported) circle function
`F' = 1_{arcSet 0 γ} · ftLp g` on the band `Icc (-γ) γ` (`Work.KMTAreas.A7Rep.envRealize` at the
half-width `δ = γ/2`); the reflection turns the character `fourier x` of `envRealize`'s inversion
formula into its conjugate `star (fourier x)`, which is what `ftLp_coeff_integral` computes `g x`
with.  The two measure-theoretic inputs are `liftMemLpTwo` (the lift of a circle `L²` function to a
bounded interval of a fundamental domain is `L²` on the line) and `fourierInvCompNeg` (reflection
of the frequency variable). -/
theorem liftOfArcSamples {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (g : ℤ → ℂ)
    (hg : Memℓp g 2)
    (hsupp : Work.BourgainPlan.IonescuWainger.HasFreqSupport g hg
      (Work.BourgainPlan.IonescuWainger.arcSet 0 γ)) :
    ∃ A : ℝ → ℂ, MeasureTheory.MemLp A 2 MeasureTheory.volume ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-γ) γ → A ξ = 0) ∧
      (∀ x : ℤ, g x = FourierTransformInv.fourierInv A (x : ℝ)) := by
  classical
  -- ## The half-width `δ = γ/2` and its band
  set δ : ℝ := γ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have h2δ : 2 * δ = γ := by rw [hδdef]; ring
  have hband : Work.KMTAreas.A7Rep.envBandSet δ = Set.Icc (-γ) γ := by
    rw [Work.KMTAreas.A7Rep.envBandSet_of_lt (by rw [hδdef]; linarith), h2δ]
  -- ## The circle function and its pointwise-supported modification
  set F : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.ftLp g hg : Circ → ℂ) with hFdef
  have hFmem : MemLp F 2 Work.Analysis.IonescuWainger.circleMeasure := by
    rw [hFdef]; exact Lp.memLp _
  have hFint : Integrable F Work.Analysis.IonescuWainger.circleMeasure :=
    hFmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hArc : MeasurableSet (Work.BourgainPlan.IonescuWainger.arcSet 0 γ) := by
    have hcont : Continuous fun θ : ℝ => (θ : Circ) := AddCircle.continuous_mk' (p := (1 : ℝ))
    have himg : Work.BourgainPlan.IonescuWainger.arcSet 0 γ
        = (fun θ : ℝ => (θ : Circ)) '' Set.Icc (-γ) γ := by
      ext ξ
      constructor
      · rintro ⟨θ, hθ, rfl⟩
        exact ⟨θ, Set.mem_Icc.mpr (abs_le.mp hθ), by simp⟩
      · rintro ⟨θ, hθ, rfl⟩
        exact ⟨θ, abs_le.mpr hθ, by simp⟩
    rw [himg]
    exact (isCompact_Icc.image hcont).isClosed.measurableSet
  set F' : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.arcSet 0 γ).indicator F with hF'def
  have hF'int : Integrable F' Work.Analysis.IonescuWainger.circleMeasure := by
    rw [hF'def]; exact hFint.indicator hArc
  have hmem_norm : ∀ ξ : Circ, ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 γ → ‖ξ‖ ≤ γ := by
    rintro ξ ⟨θ, hθ, hξ⟩
    rw [hξ, zero_add]
    exact le_trans (Work.BourgainPlan.IonescuWainger.norm_circle_coe_le_abs θ) hθ
  have hF'supp : ∀ ξ : Circ, 2 * δ < ‖ξ‖ → F' ξ = 0 := by
    intro ξ hξ
    rw [hF'def, Set.indicator_of_notMem]
    intro hmem
    exact absurd (hmem_norm ξ hmem) (not_le.mpr (by rw [h2δ] at hξ; exact hξ))
  have hF'ae : F' =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] F := by
    filter_upwards [hsupp] with ξ hξ
    rw [hF'def, hFdef]
    by_cases hmem : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 γ
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, hξ hmem]
  refine ⟨fun ξ : ℝ => Work.KMTAreas.A7Rep.envRealize δ F' (-ξ), ?_, ?_, ?_⟩
  · -- ## The `L²` bound, by reflection of the one-sided lift
    have hB : MemLp ((Set.Icc (-γ) γ).indicator (fun ξ : ℝ => F ((ξ : ℝ) : Circ))) 2 volume :=
      liftMemLpTwo hFmem measurableSet_Icc (by
        intro x hx
        rw [Set.mem_Icc] at hx
        rw [Set.mem_Ioc]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hBneg : MemLp (fun ξ : ℝ =>
        (Set.Icc (-γ) γ).indicator (fun ξ : ℝ => F ((ξ : ℝ) : Circ)) (-ξ)) 2 volume :=
      hB.comp_measurePreserving (Measure.measurePreserving_neg volume)
    refine MeasureTheory.MemLp.ae_eq ?_ hBneg
    filter_upwards with ξ
    rw [Work.KMTAreas.A7Rep.envRealize_apply]
    by_cases hmem : -(ξ) ∈ Set.Icc (-γ) γ
    · have hmem2 : ((-ξ : ℝ) : Circ) ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 γ :=
        ⟨-ξ, abs_le.mpr (Set.mem_Icc.mp hmem), by simp⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by rw [hband]; exact hmem),
        hF'def, Set.indicator_of_mem hmem2]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (by rw [hband]; exact hmem)]
  · -- ## The support of the amplitude
    intro ξ hξ
    refine Work.KMTAreas.A7Rep.envRealize_eq_zero_of_notMem_Icc hδ ?_
    rw [h2δ]
    intro hmem
    have h := Set.mem_Icc.mp hmem
    exact hξ (Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
  · -- ## The samples, by the circle Fourier-inversion formula
    intro x
    have h1 : FourierTransformInv.fourierInv
        (fun ξ : ℝ => Work.KMTAreas.A7Rep.envRealize δ F' (-ξ)) (x : ℝ)
        = FourierTransformInv.fourierInv (Work.KMTAreas.A7Rep.envRealize δ F') (-(x : ℝ)) :=
      fourierInvCompNeg (Work.KMTAreas.A7Rep.envRealize δ F') (x : ℝ)
    rw [h1]
    have h2 : FourierTransformInv.fourierInv (Work.KMTAreas.A7Rep.envRealize δ F') (-(x : ℝ))
        = ∫ ξ : Circ, F' ξ * fourier (-x) ξ ∂Work.Analysis.IonescuWainger.circleMeasure := by
      simpa using Work.KMTAreas.A7Rep.fourierInv_envRealize hδ hF'int hF'supp (-x)
    rw [h2]
    have h3 : (∫ ξ : Circ, F' ξ * fourier (-x) ξ
          ∂Work.Analysis.IonescuWainger.circleMeasure)
        = ∫ ξ : Circ, F ξ * star (fourier x ξ)
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hF'ae] with ξ hξ
      rw [hξ]
      congr 1
      have hfn := fourier_neg (T := 1) (n := x) (x := ξ)
      rw [starRingEnd_apply] at hfn
      exact hfn
    rw [h3, hFdef]
    exact Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral hg x

end Work.KMTPlan.A6Clean
