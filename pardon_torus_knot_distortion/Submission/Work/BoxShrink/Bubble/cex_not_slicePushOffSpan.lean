import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample
import Submission.Work.BoxShrink.Bubble.windingOf_standard_fst_eq_zero_of_y_ne

/-!
# The span-level push-off fails for the counterexample configuration

`Work.BoxShrink.Bubble.cex_not_slicePushOff` shows that for the standard torus,
`s = 5/2`, `c = 0`, `σ = Equiv.swap 1 2`, `u = 0` the *loop-level* push-off
`Work.BoxShrink.Bubble.SlicePushOff` fails: the longitude circle `{z = -1}` of winding `(1, 0)`
lies inside the box but is not realised away from the slicing plane.

Here we prove the sharper statement that even the *span-level* input
`Work.BoxShrink.Bubble.SlicePushOffSpan` fails, i.e. that the winding span of the region inside
the box is not contained in that of the two half-regions.  The point is that every loop of the two
half-regions (which are contained in the open sets `{y > 0}` resp. `{y < 0}` of the surface, whose
`y`-coordinate is the *longitude*-free coordinate `(2 + cos φ)·sin θ`) has vanishing first winding
coordinate (`Work.BoxShrink.Bubble.windingOf_standard_fst_eq_zero_of_y_ne`), so the whole span of
the union lies in the kernel of the first-projection `ℚ² → ℚ`, whereas `(1, 0)` lies in the span of
the region inside the box (it is realised by the longitude circle).  Hence the span of the union is
strictly smaller, and `SlicePushOffSpan` is false.

This is the honest reason `SlicePushOff` is a *strictly stronger* input than the vanishing of the
winding spans: `WindingSpan` sees the `ℚ`-span of the realised windings, and the two half-regions
miss the longitude direction entirely.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **Every realised winding of the two half-regions has vanishing first (longitude)
coordinate.**  A loop of `upperRegion ∪ lowerRegion` never meets the plane `{y = 0}`
(`y = (γ t) 1`, since `σ 2 = 1`), hence its longitude winding vanishes. -/
private lemma cex_fst_eq_zero_of_mem_realizedWindings_union {k : ℤ × ℤ}
    (hk : k ∈ RealizedWindings Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0)) :
    k.1 = 0 := by
  obtain ⟨γ, hγ, hw⟩ := hk
  rw [← hw]
  apply windingOf_standard_fst_eq_zero_of_y_ne
  intro t
  have hu := hγ t
  rw [Set.mem_union] at hu
  rcases hu with h | h
  · rw [Work.BoxShrink.Core.mem_upperRegion] at h
    have hh : (0 : ℝ) < (γ.γ t) 1 := by simpa [cex_swap_two] using h.2.2
    linarith
  · rw [Work.BoxShrink.Core.mem_lowerRegion] at h
    have hh : (γ.γ t) 1 < 0 := by simpa [cex_swap_two] using h.2.2
    linarith

/-- **`(1, 0)` is not in the winding span of the two half-regions**: the span is contained in the
kernel of the first projection of `ℚ²`. -/
private lemma cex_onezero_not_mem_windingSpan_union :
    ((((1 : ℤ) : ℚ)), ((0 : ℤ) : ℚ)) ∉
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0) := by
  intro hmem
  have hle : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) ≤ LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
    rw [Work.SurgeryInvariance.WindingSpan]
    apply Submodule.span_le.mpr
    rintro v ⟨γ, hγ, rfl⟩
    have hk := cex_fst_eq_zero_of_mem_realizedWindings_union
      (k := Work.SurgeryInvariance.windingOf Work.CoreTopology.standard γ) ⟨γ, hγ, rfl⟩
    exact LinearMap.mem_ker.mpr (by simpa using hk)
  exact absurd (hle hmem) (by simp)

/-- **`(1, 0)` lies in the winding span of the region inside the box**: it is the winding of the
longitude circle `{z = -1}`, which lies inside the box. -/
private lemma cex_onezero_mem_windingSpan_boxRegion :
    ((((1 : ℤ) : ℚ)), ((0 : ℤ) : ℚ)) ∈
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2)) := by
  rw [Work.SurgeryInvariance.WindingSpan]
  apply Submodule.subset_span
  obtain ⟨γ, hγ, hw⟩ := cex_onezero_mem_realizedWindings
  exact ⟨γ, hγ, by rw [hw]⟩

/-- **The span-level push-off fails for the counterexample configuration.** -/
theorem cex_not_slicePushOffSpan :
    ¬ SlicePushOffSpan Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 := by
  intro h
  exact cex_onezero_not_mem_windingSpan_union (h cex_onezero_mem_windingSpan_boxRegion)

end

end Work.BoxShrink.Bubble
