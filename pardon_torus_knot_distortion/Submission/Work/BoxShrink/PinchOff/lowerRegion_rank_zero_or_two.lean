import Mathlib
import Submission.Work.BoxShrink.Pinch.HalfDichotomy
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
import Submission.Work.BoxShrink.PinchOff.niceLevel_boxRegion_rank_zero_or_two

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The lower half-region `Ω₋` is the sublevel region `{lowerLevel < 0}` of the level function
`lowerLevel = max (boxNorm - s) (planeCoord)` (compare `Work.BoxShrink.Pinch.region_lowerLevel`,
which is the same statement with `region` in place of `carrier ∩ {· < 0}`). -/
theorem lowerRegion_eq_carrier_inter (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u =
      (Work.Smooth.Morse.torus ψ).carrier ∩
        {y : R3 | Work.BoxShrink.Pinch.lowerLevel s c σ u y < 0} := by
  rw [← Work.BoxShrink.Pinch.region_lowerLevel (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)]
  rfl

/-- **The rank of the lower region at a nice level is `0` or `2`.**

The lower half-region is the sublevel region of the level function
`lowerLevel = max (boxNorm - s) (planeCoord)`.  If the level set `{lowerLevel = 0}` is nice and
carries no essential loop of the surface, then the winding span of the lower region is `⊥` or `⊤`:
the surface is split by the level circles into the lower region and its open complement, and the
circles are inessential, so one of the two pieces either misses `H₁` entirely or carries all of it
(`windingSpan_bot_or_top_of_inessential_boundary`). -/
theorem lowerRegion_rank_zero_or_two (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.lowerLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (Work.BoxShrink.Pinch.lowerLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  obtain ⟨n, γ, hsimple, hdisj, hZeq⟩ := hnice.circleUnion
  -- the circles of the level set are inessential, since the level set carries no essential loop
  have hess : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (γ i) := by
    intro i hi
    exact htrace ⟨γ i, hi, fun t => by
      rw [hZeq]
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩⟩
  -- the two pieces of the complement of the level set
  set Y : Set R3 := (Work.Smooth.Morse.torus ψ).carrier ∩
    {y : R3 | 0 < Work.BoxShrink.Pinch.lowerLevel s c σ u y} with hYdef
  have hYopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) Y := by
    rw [hYdef]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (isOpen_lt continuous_const
        (Work.BoxShrink.Pinch.lowerLevel_continuous s c σ u))
  have hXeq := lowerRegion_eq_carrier_inter ψ s c σ u
  have hXY : Disjoint (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) Y := by
    rw [Set.disjoint_left]
    rintro y hy hy'
    rw [hXeq] at hy
    rw [hYdef] at hy'
    have h1 : Work.BoxShrink.Pinch.lowerLevel s c σ u y < 0 := hy.2
    have h2 : 0 < Work.BoxShrink.Pinch.lowerLevel s c σ u y := hy'.2
    linarith
  have hcover : (Work.Smooth.Morse.torus ψ).carrier \ (⋃ i, Set.range (γ i).γ)
      = Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪ Y := by
    rw [← hZeq]
    ext y
    constructor
    · intro hy
      rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet] at hy
      have hyc : y ∈ (Work.Smooth.Morse.torus ψ).carrier := hy.1
      have hne : Work.BoxShrink.Pinch.lowerLevel s c σ u y ≠ 0 := fun h => hy.2 ⟨hyc, h⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl (by rw [hXeq]; exact ⟨hyc, h⟩)
      · exact Or.inr (by rw [hYdef]; exact ⟨hyc, h⟩)
    · intro hy
      rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet]
      rcases hy with hy | hy
      · rw [hXeq] at hy
        exact ⟨hy.1, fun h => absurd h.2 (ne_of_lt hy.2)⟩
      · rw [hYdef] at hy
        exact ⟨hy.1, fun h => absurd h.2 (ne_of_gt hy.2)⟩
  exact windingSpan_bot_or_top_of_inessential_boundary (P := Work.Smooth.Morse.torus ψ)
    (X := Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) (Y := Y)
    hsimple hess hdisj
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)
    hYopen hXY hcover

end Work.BoxShrink.PinchOff
