import Mathlib

open scoped Interval
open MeasureTheory

namespace Work.RPB.B1a

/-- Continuity of a parametric interval integral: if `(w, t) ↦ F w t` is continuous on
`s ×ˢ [a, b]`, then `w ↦ ∫ t in a..b, F w t` is continuous on `s`.

This is the `ContinuousOn` version of `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
(where the integrand has to be continuous on all of `X × ℝ`).  The proof is the usual
"uniform closeness on the compact interval" argument, using `IsCompact.mem_uniformity_of_prod`
to turn continuity on `s ×ˢ [a, b]` into smallness of `‖F w t - F w₀ t‖`, uniform for
`t ∈ [a, b]` and `w` close to `w₀` within `s`. -/
theorem continuousOn_intervalIntegral {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℂ} {s : Set X} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn (Function.uncurry F) (s ×ˢ Set.Icc a b)) :
    ContinuousOn (fun w => ∫ t in a..b, F w t) s := by
  -- Every slice at a point of `s` is interval integrable.
  have hInt (w : X) (hw : w ∈ s) : IntervalIntegrable (fun t : ℝ => F w t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    have hmap : Set.MapsTo (fun t : ℝ => (w, t)) (Set.uIcc a b) (s ×ˢ Set.Icc a b) := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨hw, ht⟩
    have hc : ContinuousOn (fun t : ℝ => (w, t)) (Set.uIcc a b) :=
      (continuous_const.prodMk continuous_id).continuousOn
    exact hF.comp hc hmap
  intro w₀ hw₀
  refine Metric.tendsto_nhds.2 (fun ε hε => ?_)
  set δ : ℝ := ε / (b - a + 1) with hδdef
  have hC : (0 : ℝ) < b - a + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  -- Uniform closeness of the slices for `w` near `w₀` within `s`.
  obtain ⟨v, hv_mem, hv⟩ := IsCompact.mem_uniformity_of_prod isCompact_Icc hF hw₀
    (Metric.dist_mem_uniformity hδpos)
  refine Filter.eventually_of_mem (Filter.inter_mem hv_mem self_mem_nhdsWithin) (fun w hw => ?_)
  have hwv : w ∈ v := hw.1
  have hws : w ∈ s := hw.2
  have hwF : IntervalIntegrable (fun t : ℝ => F w t) volume a b := hInt w hws
  have hwF₀ : IntervalIntegrable (fun t : ℝ => F w₀ t) volume a b := hInt w₀ hw₀
  have hsub : ∫ t in a..b, (F w t - F w₀ t) = (∫ t in a..b, F w t) - (∫ t in a..b, F w₀ t) :=
    intervalIntegral.integral_sub hwF hwF₀
  have hnorm : ‖∫ t in a..b, (F w t - F w₀ t)‖ ≤ ∫ t in a..b, ‖F w t - F w₀ t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hmono : ∫ t in a..b, ‖F w t - F w₀ t‖ ≤ ∫ t in a..b, δ := by
    refine intervalIntegral.integral_mono_on hab ((hwF.sub hwF₀).norm) intervalIntegrable_const ?_
    intro t ht
    exact le_of_lt (by simpa [dist_eq_norm] using hv w hwv t ht)
  have hconst : ∫ t in a..b, δ = (b - a) * δ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hfin : (b - a) * δ < ε := by
    rw [hδdef]
    rw [show (b - a) * (ε / (b - a + 1)) = ((b - a) * ε) / (b - a + 1) from
      (mul_div_assoc _ _ _).symm, div_lt_iff₀ hC]
    nlinarith [hε]
  calc dist (∫ t in a..b, F w t) (∫ t in a..b, F w₀ t)
      = ‖∫ t in a..b, (F w t - F w₀ t)‖ := by rw [dist_eq_norm, ← hsub]
    _ ≤ ∫ t in a..b, ‖F w t - F w₀ t‖ := hnorm
    _ ≤ (b - a) * δ := by rw [← hconst]; exact hmono
    _ < ε := hfin

end Work.RPB.B1a
