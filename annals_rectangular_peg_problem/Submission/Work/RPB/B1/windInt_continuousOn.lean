import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.RPB.B1

theorem windInt_continuousOn (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    ContinuousOn (Work.RPB.B1.windInt u) ((Set.range u)ᶜ) := by
  intro q₀ hq₀
  have hcont_u : Continuous u := hu.continuous
  have hcont_du : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hGcont : Continuous (fun t : ℝ => ‖u t - q₀‖) := (hcont_u.sub continuous_const).norm
  have hHcont : Continuous (fun t : ℝ => ‖deriv u t‖) := hcont_du.norm
  -- a point where the distance from `q₀` to the compact piece `u '' uIcc 0 (2π)` is attained
  obtain ⟨t₁, ht₁, hmin⟩ := IsCompact.exists_isMinOn (s := Set.uIcc (0 : ℝ) (2 * Real.pi))
    isCompact_uIcc Set.nonempty_uIcc hGcont.continuousOn
  -- a point where `‖deriv u‖` is maximal on the compact interval
  obtain ⟨t₂, ht₂, hmax⟩ := IsCompact.exists_isMaxOn (s := Set.uIcc (0 : ℝ) (2 * Real.pi))
    isCompact_uIcc Set.nonempty_uIcc hHcont.continuousOn
  let δ₀ : ℝ := ‖u t₁ - q₀‖
  let M : ℝ := ‖deriv u t₂‖
  let C : ℝ := M / (δ₀ / 2)
  have hδ₀pos : 0 < δ₀ := by
    change 0 < ‖u t₁ - q₀‖
    rw [norm_pos_iff]
    intro h
    exact hq₀ ⟨t₁, sub_eq_zero.mp h⟩
  have hMnn : 0 ≤ M := by
    change 0 ≤ ‖deriv u t₂‖
    exact norm_nonneg _
  -- measurability of the integrand in the spatial variable
  have hmeas : ∀ᶠ x in nhdsWithin q₀ ((Set.range u)ᶜ),
      AEStronglyMeasurable (fun t : ℝ => (deriv u t / (u t - x)).im)
        (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : Measurable (fun t : ℝ => deriv u t / (u t - x)) :=
      hcont_du.measurable.div ((hcont_u.sub continuous_const).measurable)
    exact (Complex.measurable_im.comp h1).aestronglyMeasurable
  -- a uniform bound for `x` in a neighbourhood of `q₀`
  have hbound : ∀ᶠ x in nhdsWithin q₀ ((Set.range u)ᶜ),
      ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
        ‖(deriv u t / (u t - x)).im‖ ≤ (fun _ : ℝ => C) t := by
    have hW : Metric.ball q₀ (δ₀ / 2) ∈ nhdsWithin q₀ ((Set.range u)ᶜ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds q₀ (by positivity))
    refine Filter.eventually_of_mem hW (fun x hx => ?_)
    refine Filter.Eventually.of_forall (fun t htI => ?_)
    have hxt : ‖x - q₀‖ < δ₀ / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx
    have htu : t ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := Set.uIoc_subset_uIcc htI
    have hmin' : δ₀ ≤ ‖u t - q₀‖ := by
      change ‖u t₁ - q₀‖ ≤ ‖u t - q₀‖
      exact hmin htu
    have hmax' : ‖deriv u t‖ ≤ M := by
      change ‖deriv u t‖ ≤ ‖deriv u t₂‖
      exact hmax htu
    have h1 : ‖u t - q₀‖ ≤ ‖u t - x‖ + ‖x - q₀‖ := by
      have := norm_add_le (u t - x) (x - q₀)
      rwa [show u t - x + (x - q₀) = u t - q₀ from by ring] at this
    have hhalf : δ₀ / 2 < ‖u t - x‖ := by linarith
    have hδhalf_pos : 0 < δ₀ / 2 := by linarith
    calc ‖(deriv u t / (u t - x)).im‖
        ≤ ‖deriv u t / (u t - x)‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
      _ = ‖deriv u t‖ / ‖u t - x‖ := norm_div _ _
      _ ≤ M / (δ₀ / 2) := div_le_div₀ hMnn hmax' hδhalf_pos (le_of_lt hhalf)
      _ = (fun _ : ℝ => C) t := rfl
  -- the integrand is continuous in the spatial variable, for every `t`
  have hcont : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ContinuousWithinAt (fun x : ℂ => (deriv u t / (u t - x)).im) ((Set.range u)ᶜ) q₀ := by
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    have hut : u t ≠ q₀ := fun h => hq₀ ⟨t, h⟩
    have hd : ContinuousAt (fun x : ℂ => deriv u t / (u t - x)) q₀ := by
      refine ContinuousAt.div continuousAt_const ?_ ?_
      · exact (continuous_const.sub continuous_id).continuousAt
      · rw [sub_ne_zero]; exact hut
    exact (Complex.continuous_im.continuousAt.comp hd).continuousWithinAt
  have hmain : ContinuousWithinAt
      (fun x : ℂ => ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - x)).im)
      ((Set.range u)ᶜ) q₀ :=
    intervalIntegral.continuousWithinAt_of_dominated_interval hmeas hbound
      intervalIntegrable_const hcont
  have hconst := hmain.const_mul (1 / (2 * Real.pi))
  change ContinuousWithinAt
      (fun q => (1 / (2 * Real.pi)) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im) ((Set.range u)ᶜ) q₀
  exact hconst

end Work.RPB.B1
