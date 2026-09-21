import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral

open MeasureTheory Filter
open scoped Interval Topology

namespace Commons.Analysis.Radon

/-- FTC plus chain rule: if `h` is interval-integrable on `(0,u²)` and continuous at `u²`,
then the derivative of `u ↦ ∫_0^{u²} h` is `h(u²) · 2u`. -/
lemma hasDerivAt_integral_sq {h : ℝ → ℝ} {u : ℝ} (hu : 0 < u)
    (hint : IntervalIntegrable h volume (0:ℝ) (u ^ 2))
    (hmeas : StronglyMeasurableAtFilter h (𝓝 (u ^ 2)) volume)
    (hcont : ContinuousAt h (u ^ 2)) :
    HasDerivAt (fun u : ℝ => ∫ t in (0:ℝ)..(u ^ 2), h t) (h (u ^ 2) * (2 * u)) u := by
  let g : ℝ → ℝ := fun u => u ^ 2
  have h1 : HasDerivAt (fun w : ℝ => ∫ t in (0:ℝ)..w, h t) (h (g u)) (g u) := by
    dsimp [g]
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have h2 : HasDerivAt g (2 * u) u := by
    dsimp [g]
    simpa using hasDerivAt_pow 2 u
  have hcomp : HasDerivAt ((fun w : ℝ => ∫ t in (0:ℝ)..w, h t) ∘ g) ((2 * u) * h (g u)) u :=
    h1.scomp u h2
  simpa [g, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- Differentiation of the singular profile integral in the `d = 3` inversion. -/
lemma hasDerivAt_integral_sqrt_profile {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun u : ℝ => ∫ t in (0:ℝ)..(u ^ 2), G (Real.sqrt t) / Real.sqrt t)
      (G u / u * (2 * u)) u := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have hu_sq_mem : u ^ 2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hcont : ContinuousAt (fun t : ℝ => G (Real.sqrt t) / Real.sqrt t) (u ^ 2) := by
    have hsqrt_cont : ContinuousAt (fun t : ℝ => Real.sqrt t) (u ^ 2) := Real.continuous_sqrt.continuousAt
    have hG_cont : ContinuousAt G (Real.sqrt (u ^ 2)) := by
      rw [Real.sqrt_sq hu0.le]
      exact hG.continuousAt (Icc_mem_nhds hu0 hu1)
    have hcomp : ContinuousAt (fun t : ℝ => G (Real.sqrt t)) (u ^ 2) :=
      hG_cont.comp hsqrt_cont
    exact hcomp.div hsqrt_cont (by rw [Real.sqrt_sq hu0.le]; exact ne_of_gt hu0)
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => G (Real.sqrt t) / Real.sqrt t)
      (𝓝 (u ^ 2)) volume := by
    refine ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (0:ℝ) 1) isOpen_Ioo ?_ (u ^ 2) hu_sq_mem
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hsqrt_cont : ContinuousAt (fun t : ℝ => Real.sqrt t) t := Real.continuous_sqrt.continuousAt
    have hG_cont : ContinuousAt G (Real.sqrt t) := by
      apply hG.continuousAt
      apply Icc_mem_nhds
      · exact Real.sqrt_pos.2 ht0
      · calc Real.sqrt t < Real.sqrt 1 := Real.sqrt_lt_sqrt ht0.le ht1
          _ = 1 := Real.sqrt_one
    exact (hG_cont.comp hsqrt_cont).div hsqrt_cont (ne_of_gt (Real.sqrt_pos.2 ht0))
  have hG_bound : ∃ C, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖G t‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.norm
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  obtain ⟨C, hC⟩ := hG_bound
  have hC_nonneg : 0 ≤ C := by
    obtain ⟨t, ht⟩ := Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)
    exact le_trans (norm_nonneg _) (hC t ht)
  have hbound_int : IntervalIntegrable (fun t : ℝ => C * (Real.sqrt t)⁻¹) volume (0:ℝ) (u ^ 2) := by
    have h := Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := (0:ℝ)) (b := u ^ 2) (by nlinarith)
    simpa [mul_comm] using h.const_mul C
  have hfm : AEStronglyMeasurable (fun t : ℝ => G (Real.sqrt t) / Real.sqrt t)
      (volume.restrict (Set.uIoc (0:ℝ) (u ^ 2))) := by
    have hcontOn : ContinuousOn (fun t : ℝ => G (Real.sqrt t) / Real.sqrt t) (Set.Ioc (0:ℝ) (u ^ 2)) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htle : t ≤ u ^ 2 := ht.2
      have hsqrt_cont : ContinuousAt (fun t : ℝ => Real.sqrt t) t := Real.continuous_sqrt.continuousAt
      have hG_cont : ContinuousAt G (Real.sqrt t) := by
        apply hG.continuousAt
        apply Icc_mem_nhds
        · exact Real.sqrt_pos.2 ht0
        · have hsqrt_lt : Real.sqrt t < 1 := by
            calc Real.sqrt t ≤ Real.sqrt (u ^ 2) := Real.sqrt_le_sqrt htle
              _ = u := Real.sqrt_sq hu0.le
              _ < 1 := hu1
          exact hsqrt_lt
      exact ((hG_cont.comp hsqrt_cont).div hsqrt_cont (ne_of_gt (Real.sqrt_pos.2 ht0))).continuousWithinAt
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ u ^ 2)]
    exact (hcontOn.mono (by intro t ht; exact ht)).aestronglyMeasurable measurableSet_Ioc
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0:ℝ) (u ^ 2))),
      ‖G (Real.sqrt t) / Real.sqrt t‖ ≤ C * (Real.sqrt t)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht0 : 0 < t := by
      rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ u ^ 2)] at ht
      exact ht.1
    have htle : t ≤ u ^ 2 := by
      rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ u ^ 2)] at ht
      exact ht.2
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hsqrt_le : Real.sqrt t ≤ 1 := by
      calc Real.sqrt t ≤ Real.sqrt (u ^ 2) := Real.sqrt_le_sqrt htle
        _ = u := Real.sqrt_sq hu0.le
        _ ≤ 1 := hu1.le
    have hG_le : ‖G (Real.sqrt t)‖ ≤ C := hC (Real.sqrt t) ⟨Real.sqrt_nonneg t, hsqrt_le⟩
    have hnorm : ‖G (Real.sqrt t) / Real.sqrt t‖ = ‖G (Real.sqrt t)‖ / Real.sqrt t := by
      rw [norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    rw [hnorm]
    calc
      ‖G (Real.sqrt t)‖ / Real.sqrt t ≤ C / Real.sqrt t := by gcongr
      _ = C * (Real.sqrt t)⁻¹ := by rw [div_eq_mul_inv]
  have hint : IntervalIntegrable (fun t : ℝ => G (Real.sqrt t) / Real.sqrt t) volume (0:ℝ) (u ^ 2) :=
    IntervalIntegrable.mono_fun' hbound_int hfm hpoint
  have h := hasDerivAt_integral_sq (h := fun t : ℝ => G (Real.sqrt t) / Real.sqrt t) hu0 hint hmeas hcont
  simpa [Real.sqrt_sq hu0.le] using h

end Commons.Analysis.Radon
