import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

open MeasureTheory Set Filter

/-- For `z` on the circle `‖z - x₀‖ = R`, the logarithmic potential of any `B ⊆ [x₀-ρ, x₀+ρ]`
is at most `volume B · log (R/(R-ρ))`: on that circle every point of `B` is at distance at
least `R - ρ` from `z`, so the integrand `log (R/‖z - t‖)` is pointwise bounded by the
(constant) `log (R/(R-ρ))`, which is nonnegative since `R > ρ`. -/
theorem rcPot_sphere_le {B : Set ℝ} {x₀ ρ R : ℝ} (hB : B ⊆ Set.Icc (x₀ - ρ) (x₀ + ρ))
    (hρ : 0 < ρ) (hρR : ρ < R) {z : ℂ} (hz : z ∈ Metric.sphere (x₀ : ℂ) R) :
    Work.TMComp.RC.logPot B R z
      ≤ (MeasureTheory.volume B).toReal * Real.log (R / (R - ρ)) := by
  rw [Work.TMComp.RC.logPot]
  have hR : 0 < R := lt_trans hρ hρR
  have hRρ : 0 < R - ρ := sub_pos.mpr hρR
  have hzR : ‖z - (x₀ : ℂ)‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz; exact hz
  have hnorm_t : ∀ t : ℝ, ‖((t - x₀ : ℝ) : ℂ)‖ = |t - x₀| := fun t => RCLike.norm_ofReal _
  have hnorm_u : ∀ t : ℝ, ‖((x₀ - t : ℝ) : ℂ)‖ = |x₀ - t| := fun t => RCLike.norm_ofReal _
  -- Distance lower bound: every `t ∈ B` is at distance at least `R - ρ` from `z`.
  have hlow : ∀ t ∈ B, R - ρ ≤ ‖z - (t:ℂ)‖ := by
    intro t ht
    have htI := hB ht; rw [Set.mem_Icc] at htI
    have h1 : ‖z - (x₀:ℂ)‖ - ‖z - (t:ℂ)‖ ≤ ‖(z - (x₀:ℂ)) - (z - (t:ℂ))‖ := norm_sub_norm_le _ _
    have h2 : (z - (x₀:ℂ)) - (z - (t:ℂ)) = ((t - x₀ : ℝ) : ℂ) := by push_cast; ring
    rw [h2, hnorm_t t, hzR] at h1
    have h3 : |t - x₀| ≤ ρ := abs_le.mpr ⟨by linarith [htI.1], by linarith [htI.2]⟩
    linarith
  -- Distance upper bound: every `t ∈ B` is at distance at most `R + ρ` from `z`.
  have hup : ∀ t ∈ B, ‖z - (t:ℂ)‖ ≤ R + ρ := by
    intro t ht
    have htI := hB ht; rw [Set.mem_Icc] at htI
    have h3 : |x₀ - t| ≤ ρ := abs_le.mpr ⟨by linarith [htI.2], by linarith [htI.1]⟩
    have h1 : z - (t:ℂ) = (z - (x₀:ℂ)) + ((x₀:ℂ) - (t:ℂ)) := by ring
    rw [h1]
    calc ‖(z - (x₀:ℂ)) + ((x₀:ℂ) - (t:ℂ))‖
        ≤ ‖z - (x₀:ℂ)‖ + ‖(x₀:ℂ) - (t:ℂ)‖ := norm_add_le _ _
      _ = R + |x₀ - t| := by rw [hzR, ← Complex.ofReal_sub, hnorm_u t]
      _ ≤ R + ρ := by linarith
  -- Pointwise two-sided bound on the integrand.
  have hupper : ∀ t ∈ B, Real.log (R / ‖z - (t:ℂ)‖) ≤ Real.log (R / (R - ρ)) := by
    intro t ht
    have hdpos : 0 < ‖z - (t:ℂ)‖ := lt_of_lt_of_le hRρ (hlow t ht)
    exact Real.log_le_log (div_pos hR hdpos) (div_le_div_of_nonneg_left hR.le hRρ (hlow t ht))
  have hlower : ∀ t ∈ B, -Real.log (R / (R - ρ)) ≤ Real.log (R / ‖z - (t:ℂ)‖) := by
    intro t ht
    have hdpos : 0 < ‖z - (t:ℂ)‖ := lt_of_lt_of_le hRρ (hlow t ht)
    have step1 : Real.log (R / (R + ρ)) ≤ Real.log (R / ‖z - (t:ℂ)‖) :=
      Real.log_le_log (div_pos hR (by linarith)) (div_le_div_of_nonneg_left hR.le hdpos (hup t ht))
    have step2 : -Real.log (R / (R - ρ)) ≤ Real.log (R / (R + ρ)) := by
      rw [← Real.log_inv, inv_div]
      apply Real.log_le_log (div_pos hRρ hR)
      rw [div_le_div_iff₀ hR (by linarith)]
      nlinarith [sq_nonneg ρ]
    linarith
  have hf : Measurable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) := by fun_prop
  have hBfin : (volume : Measure ℝ) B ≠ ⊤ := by
    have hmono : (volume : Measure ℝ) B ≤ volume (Set.Icc (x₀ - ρ) (x₀ + ρ)) := measure_mono hB
    rw [Real.volume_Icc] at hmono
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmono
  have hCint : Integrable (fun _ : ℝ => Real.log (R / (R - ρ))) (volume.restrict B) :=
    integrableOn_const (by simp [hBfin]) (by simp)
  have hae_norm : Filter.Eventually
      (fun t : ℝ => ‖Real.log (R / ‖z - (t:ℂ)‖)‖ ≤ Real.log (R / (R - ρ)))
      (ae (volume.restrict B)) := by
    rw [ae_restrict_iff
      (p := fun t : ℝ => ‖Real.log (R / ‖z - (t:ℂ)‖)‖ ≤ Real.log (R / (R - ρ)))
      (measurableSet_le hf.norm measurable_const)]
    exact Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hlower t ht, hupper t ht⟩
  have hf_int : Integrable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) (volume.restrict B) :=
    Integrable.mono' hCint hf.aestronglyMeasurable hae_norm
  have hae_le : Filter.Eventually
      (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖) ≤ Real.log (R / (R - ρ)))
      (ae (volume.restrict B)) := by
    rw [ae_restrict_iff
      (p := fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖) ≤ Real.log (R / (R - ρ)))
      (measurableSet_le hf measurable_const)]
    exact Eventually.of_forall fun t ht => hupper t ht
  calc ∫ t in B, Real.log (R / ‖z - (t:ℂ)‖)
      ≤ ∫ t in B, Real.log (R / (R - ρ)) := integral_mono_ae hf_int hCint hae_le
    _ = (volume B).toReal * Real.log (R / (R - ρ)) := by rw [setIntegral_const, smul_eq_mul]; rfl

end Work.TMComp.RealCartan
