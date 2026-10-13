import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces

open MeasureTheory Set Filter
open scoped Topology

/-- The tail integral of a function integrable on `(1, ∞)` is continuous on `[1, ∞)`.

For `z, x₀ ∈ [1, ∞)` the difference of the tail integrals is the interval integral
`∫_{Ioi z} G - ∫_{Ioi x₀} G = ∫_{z}^{x₀} G`; the latter is continuous in `z` by the
fundamental theorem of calculus (continuous primitive of an `L¹` function). -/
theorem tail_continuous (G : ℝ → ℝ) (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) :
    ContinuousOn (fun z => ∫ s in Set.Ioi z, G s) (Set.Ici 1) := by
  intro x₀ hx₀
  have hx₀1 : (1 : ℝ) ≤ x₀ := hx₀
  have hGx₀ : IntegrableOn G (Ioi x₀) := hG.mono_set (Ioi_subset_Ioi hx₀1)
  -- On `[1, x₀+1]` the tail is `F x₀` minus the primitive `z ↦ ∫_{x₀}^{z} G`.
  have hkey : ∀ z ∈ Icc (1 : ℝ) (x₀ + 1),
      (∫ s in Ioi z, G s) = (∫ s in Ioi x₀, G s) - ∫ s in x₀..z, G s := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ z := hz.1
    have hGz : IntegrableOn G (Ioi z) := hG.mono_set (Ioi_subset_Ioi hz1)
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (f := G) (a := x₀) (b := z) hGx₀ hGz
    linarith [h]
  have hInt : IntervalIntegrable G volume (1 : ℝ) (x₀ + 1) := by
    rw [intervalIntegrable_iff]
    rw [uIoc_of_le (by linarith : (1 : ℝ) ≤ x₀ + 1)]
    exact hG.mono_set Ioc_subset_Ioi_self
  have hcont : ContinuousWithinAt (fun z => ∫ s in x₀..z, G s) (Icc (1 : ℝ) (x₀ + 1)) x₀ := by
    refine intervalIntegral.continuousWithinAt_primitive (measure_singleton x₀) ?_
    rw [min_eq_right hx₀1, max_eq_right (by linarith : x₀ ≤ x₀ + 1)]
    exact hInt
  have hF : ContinuousWithinAt (fun z => (∫ s in Ioi x₀, G s) - ∫ s in x₀..z, G s)
      (Icc (1 : ℝ) (x₀ + 1)) x₀ :=
    continuousWithinAt_const.sub hcont
  have hEq : (fun z => ∫ s in Ioi z, G s) =ᶠ[𝓝[Icc (1 : ℝ) (x₀ + 1)] x₀]
      (fun z => (∫ s in Ioi x₀, G s) - ∫ s in x₀..z, G s) :=
    eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => hkey z hz)
  have hF2 : ContinuousWithinAt (fun z => ∫ s in Ioi z, G s) (Icc (1 : ℝ) (x₀ + 1)) x₀ := by
    refine hF.congr_of_eventuallyEq hEq ?_
    simp [intervalIntegral.integral_same]
  -- `Icc 1 (x₀+1)` is a neighbourhood of `x₀` within `Ici 1`, so we may enlarge the set.
  have hmem : Icc (1 : ℝ) (x₀ + 1) ∈ 𝓝[Ici (1 : ℝ)] x₀ := by
    rw [mem_nhdsWithin]
    exact ⟨Iio (x₀ + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, le_of_lt hx.1⟩⟩
  exact hF2.mono_of_mem_nhdsWithin hmem

end Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces
