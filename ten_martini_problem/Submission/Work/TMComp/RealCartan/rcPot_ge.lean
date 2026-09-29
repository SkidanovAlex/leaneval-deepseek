import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

open MeasureTheory Set Filter
open scoped ENNReal

/-- The logarithmic potential of a set `B` contained in `[x₀ - ρ, x₀ + ρ]` at scale `R`,
evaluated at a point `x` with `|x - x₀| ≤ r`, is bounded below by the measure of `B` times
`log (R / (ρ + r))`: every point `t ∈ B` lies within distance `ρ + r` of `x`, so the
integrand `log (R / ‖x - t‖)` dominates the constant `log (R / (ρ + r))`. -/
theorem rcPot_ge {B : Set ℝ} {x₀ ρ r R : ℝ} (hB : B ⊆ Set.Icc (x₀ - ρ) (x₀ + ρ))
    (hρ : 0 < ρ) (hr : 0 ≤ r) (hR : 0 < R) {x : ℝ} (hx : |x - x₀| ≤ r) :
    (MeasureTheory.volume B).toReal * Real.log (R / (ρ + r))
      ≤ Work.TMComp.RC.logPot B R (x : ℂ) := by
  have hab : x₀ - ρ ≤ x₀ + ρ := by linarith
  -- `log (R / ‖x - t‖) = log (R / (t - x))` for every `t`
  have hlog : ∀ t : ℝ, Real.log (R / ‖(x:ℂ) - (t:ℂ)‖) = Real.log (R / (t - x)) := by
    intro t
    rw [show ‖(x:ℂ) - (t:ℂ)‖ = |x - t| by
      rw [show (x:ℂ) - (t:ℂ) = ((x - t : ℝ) : ℂ) by rw [Complex.ofReal_sub]]
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]]
    rw [← Real.log_abs (R / (t - x)), abs_div, abs_sub_comm, abs_of_pos hR]
  -- integrability of the potential: it is `log ∘ (t ↦ R / (t - x))`, a meromorphic argument
  have hmer : MeromorphicOn (fun t : ℝ => R / (t - x)) (Set.uIcc (x₀ - ρ) (x₀ + ρ)) := by
    have h1 : MeromorphicOn (fun t : ℝ => t - x) (Set.uIcc (x₀ - ρ) (x₀ + ρ)) :=
      MeromorphicOn.sub MeromorphicOn.id (MeromorphicOn.const x)
    exact MeromorphicOn.div (MeromorphicOn.const R) h1
  have hII : IntervalIntegrable (fun t : ℝ => Real.log (R / (t - x))) volume (x₀ - ρ) (x₀ + ρ) :=
    MeromorphicOn.intervalIntegrable_log hmer
  have hFint : IntegrableOn (fun t : ℝ => Real.log (R / ‖(x:ℂ) - (t:ℂ)‖)) B volume := by
    have h1 : (fun t : ℝ => Real.log (R / ‖(x:ℂ) - (t:ℂ)‖))
        = fun t : ℝ => Real.log (R / (t - x)) := funext hlog
    rw [h1]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hII).mono_set hB
  -- pointwise bound off the single point `x`
  have hpt : ∀ t ∈ B, t ≠ x → Real.log (R / (ρ + r)) ≤ Real.log (R / ‖(x:ℂ) - (t:ℂ)‖) := by
    intro t htB htx
    have htI : t ∈ Set.Icc (x₀ - ρ) (x₀ + ρ) := hB htB
    have hxlo : x₀ - r ≤ x := by linarith [(abs_le.mp hx).1]
    have hxhi : x ≤ x₀ + r := by linarith [(abs_le.mp hx).2]
    have hxt : |x - t| ≤ ρ + r := by
      rw [abs_le]; constructor <;> linarith [htI.1, htI.2]
    have hpos : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htx))
    have hdiv : R / (ρ + r) ≤ R / |x - t| :=
      div_le_div_of_nonneg_left (le_of_lt hR) hpos hxt
    have h2 : Real.log (R / (t - x)) = Real.log (R / |x - t|) := by
      rw [← Real.log_abs (R / (t - x)), abs_div, abs_of_pos hR, abs_sub_comm]
    rw [hlog t, h2]
    exact Real.log_le_log (by positivity) hdiv
  -- `B` has finite measure
  have hvolB : volume B < ⊤ := by
    calc volume B ≤ volume (Set.Icc (x₀ - ρ) (x₀ + ρ)) := measure_mono hB
      _ = ENNReal.ofReal ((x₀ + ρ) - (x₀ - ρ)) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- the constant function is integrable on `B`
  have hcint : Integrable (fun _ : ℝ => Real.log (R / (ρ + r))) (volume.restrict B) := by
    rw [integrable_const_iff]
    refine Or.inr ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hvolB
  -- the bound holds almost everywhere
  have hae : (fun _ : ℝ => Real.log (R / (ρ + r)))
      ≤ᵐ[volume.restrict B] (fun t : ℝ => Real.log (R / ‖(x:ℂ) - (t:ℂ)‖)) := by
    have hFmeas : Measurable (fun t : ℝ => Real.log (R / ‖(x:ℂ) - (t:ℂ)‖)) := by
      rw [show (fun t : ℝ => Real.log (R / ‖(x:ℂ) - (t:ℂ)‖))
        = fun t : ℝ => Real.log (R / (t - x)) from funext hlog]
      fun_prop
    have hmeas : MeasurableSet {t : ℝ | Real.log (R / (ρ + r)) ≤ Real.log (R / ‖(x:ℂ) - (t:ℂ)‖)} :=
      hFmeas measurableSet_Ici
    rw [Filter.EventuallyLE, ae_restrict_iff hmeas, ae_iff]
    apply measure_mono_null _ (measure_singleton x)
    intro t ht
    rw [Set.mem_ofPred_eq, Classical.not_imp] at ht
    obtain ⟨htB, htc⟩ := ht
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact htc (hpt t htB hne)
  -- assemble
  have hsub := integral_sub hFint hcint
  have hnn : 0 ≤ ∫ t, (Real.log (R / ‖(x:ℂ) - (t:ℂ)‖) - Real.log (R / (ρ + r)))
      ∂(volume.restrict B) :=
    integral_nonneg_of_ae (hae.mono (fun t ht => sub_nonneg.mpr ht))
  have hcval : ∫ _ : ℝ, Real.log (R / (ρ + r)) ∂(volume.restrict B)
      = (volume B).toReal * Real.log (R / (ρ + r)) := by
    rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul]
  have hkey : (volume B).toReal * Real.log (R / (ρ + r))
      ≤ ∫ t, Real.log (R / ‖(x:ℂ) - (t:ℂ)‖) ∂(volume.restrict B) := by
    linarith [hsub, hnn, hcval]
  simpa [Work.TMComp.RC.logPot] using hkey

end Work.TMComp.RealCartan
