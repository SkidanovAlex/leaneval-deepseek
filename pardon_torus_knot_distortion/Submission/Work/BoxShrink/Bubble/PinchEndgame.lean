import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.cex_upperRegion_essential
import Submission.Work.BoxShrink.Bubble.cex_not_slicePushOffSpan

/-!
# Why the endgame field of the pinch datum is necessary

`Work.BoxShrink.Bubble.PinchDatum` requires Pardon's dichotomy
(`Work.BoxShrink.Bubble.PardonDichotomy`) at every parameter *before* the pinching parameter
(`Work.BoxShrink.Bubble.SweepLoopsSmall.dichotomy` is quantified over `t < 1`), and separately asks
for the endgame `Work.BoxShrink.Bubble.PinchDatum.pinch`: at the pinching parameter the region
changes from a genuine sphere's inside to the union of the two half-regions by a piece of dimension
at most one.

This file proves that the restriction is essential: **at the counterexample configuration the
dichotomy fails for the region at the pinching parameter**, i.e. for
`upperRegion ∪ lowerRegion`, whose winding span is the single line `ℚ·(0,1)` — not `⊥` (it contains
the meridian of winding `(0,1)`) and not `⊤` (its span is contained in the kernel of the first
projection `ℚ² → ℚ`, so it misses `(1,0)`).  Hence a formulation of the pinch datum requiring the
dichotomy at *every* parameter would be refuted at the counterexample configuration, and the
endgame has to be carried by `PinchDatum.pinch` instead — exactly as in Pardon's proof, where the
last step is an *inclusion* argument ("this component is contained in the interior of one of the two
spheres that comprise `S₁`"), not the dichotomy.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **Every realised winding of the two half-regions of the counterexample configuration has
vanishing first (longitude) coordinate**: a loop of `upperRegion ∪ lowerRegion` never meets the
plane `{y = 0}` (`y` is the coordinate `(γ t) 1`, because `σ 2 = 1`), so
`Work.BoxShrink.Bubble.windingOf_standard_fst_eq_zero_of_y_ne` applies. -/
theorem cex_union_fst_eq_zero {k : ℤ × ℤ}
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

/-- The winding span of the two half-regions of the counterexample configuration is contained in
the kernel of the first projection of `ℚ²`. -/
theorem cex_windingSpan_union_le_ker :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) ≤ LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
  rw [Work.SurgeryInvariance.WindingSpan]
  apply Submodule.span_le.mpr
  rintro v ⟨γ, hγ, rfl⟩
  have hk := cex_union_fst_eq_zero
    (k := Work.SurgeryInvariance.windingOf Work.CoreTopology.standard γ) ⟨γ, hγ, rfl⟩
  exact LinearMap.mem_ker.mpr (by simpa using hk)

/-- `(1,0)` is not in the winding span of the two half-regions. -/
theorem cex_onezero_not_mem_windingSpan_union :
    ((((1 : ℤ) : ℚ)), ((0 : ℤ) : ℚ)) ∉
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0) :=
  fun hmem => absurd (cex_windingSpan_union_le_ker hmem) (by simp)

/-- **Pardon's dichotomy fails at the pinching parameter of the counterexample configuration.**
The winding span of `upperRegion ∪ lowerRegion` is the line `ℚ·(0,1)`: it is nonzero (it contains the
meridian of winding `(0,1)`, `Work.BoxShrink.Bubble.cex_upperRegion_essential`) and it is not `⊤`
(it misses `(1,0)`).  This is why `Work.BoxShrink.Bubble.PinchDatum` requires the dichotomy only for
`t < 1` and carries the endgame in `Work.BoxShrink.Bubble.PinchDatum.pinch`. -/
theorem cex_not_pardonDichotomy_union :
    ¬ PardonDichotomy Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) := by
  intro h
  rcases h with h | h
  · exact ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr
      (Work.CoreTopology.ContainsEssentialLoop.mono Set.subset_union_left
        cex_upperRegion_essential)) h
  · exact cex_onezero_not_mem_windingSpan_union (h ▸ Submodule.mem_top)

end

end Work.BoxShrink.Bubble
