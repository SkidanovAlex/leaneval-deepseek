import Mathlib
import Submission.Work.BoxShrink.Pinch.HalfDichotomy
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
import Submission.Work.BoxShrink.PinchOff.niceLevel_boxRegion_rank_zero_or_two

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The complement of a level set in the surface is the sublevel region together with the
superlevel region.**  For any exact level function `g` and level `0`, the points of the surface at
which `g` does not vanish split into the open region `{g < 0}` and the open region `{g > 0}`.

This is the analogue, for an arbitrary level function, of `carrier_sdiff_levelSet` in
`niceLevel_boxRegion_rank_zero_or_two.lean` (which treats the box norm).  It is what allows the
boundary of the region `region ψ g 0` — a nice level set — to be split into two open pieces, so that
`windingSpan_bot_or_top_of_inessential_boundary` applies. -/
theorem carrier_sdiff_levelSet_eq_region_union (ψ : Submission.Diffeo) (g : R3 → ℝ) :
    (Work.Smooth.Morse.torus ψ).carrier \ Work.Smooth.Morse.levelSet ψ g 0 =
      Work.Smooth.Morse.region ψ g 0 ∪
        ((Work.Smooth.Morse.torus ψ).carrier ∩ {x : R3 | 0 < g x}) := by
  ext x
  simp only [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet, Set.mem_union,
    Work.Smooth.Morse.region, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hne⟩
    rcases lt_or_gt_of_ne (fun h => hne ⟨hx, h⟩) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨hx, fun hc => absurd hc.2 (ne_of_lt h)⟩
    · exact ⟨hx, fun hc => absurd hc.2 (ne_of_gt h)⟩

/-- **The upper region of the pinch carries no loop or the whole of `H₁`: Pardon's dichotomy at the
upper half-box sphere.**

The upper region `upperRegion (torus ψ) s c σ u` is the level-`0` sublevel region of the level
function `upperLevel s c σ u = max (boxNorm - s) (-planeCoord)` (`region_upperLevel`).  If that
level set is *nice* and carries no essential loop of the surface, then it is a finite disjoint union
of simple closed curves, all inessential; the two sides of it in the surface are the upper region
and the open superlevel region `{0 < upperLevel}`, both open in the carrier and disjoint, and their
union is the complement of the level set.  So `windingSpan_bot_or_top_of_inessential_boundary`
applies and the winding span is `⊥` or `⊤`. -/
theorem upperRegion_rank_zero_or_two (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  obtain ⟨n, γ, hsimple, hdisj, hZeq⟩ := hnice.circleUnion
  -- every circle of the level set is inessential, since the level set carries no essential loop
  have hess : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (γ i) := by
    intro i hi
    exact htrace ⟨γ i, hi, fun t => by
      rw [hZeq]; exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩⟩
  -- the sublevel region of `upperLevel` is open in the carrier
  have hX : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0) :=
    Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (P := Work.Smooth.Morse.torus ψ)
      (b := {x : R3 | Work.BoxShrink.Pinch.upperLevel s c σ u x < 0})
      (isOpen_lt (Work.BoxShrink.Pinch.upperLevel_continuous s c σ u) continuous_const)
  -- and so is the open superlevel region `{0 < upperLevel}`
  have hY : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ)
      ((Work.Smooth.Morse.torus ψ).carrier ∩
        {x : R3 | 0 < Work.BoxShrink.Pinch.upperLevel s c σ u x}) :=
    Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (P := Work.Smooth.Morse.torus ψ)
      (b := {x : R3 | 0 < Work.BoxShrink.Pinch.upperLevel s c σ u x})
      (isOpen_lt continuous_const (Work.BoxShrink.Pinch.upperLevel_continuous s c σ u))
  -- the two pieces are disjoint
  have hXY : Disjoint (Work.Smooth.Morse.region ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0)
      ((Work.Smooth.Morse.torus ψ).carrier ∩
        {x : R3 | 0 < Work.BoxShrink.Pinch.upperLevel s c σ u x}) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Work.Smooth.Morse.mem_region] at hx
    exact absurd hx.2 (not_lt.mpr hx'.2.le)
  -- and they cover the complement of the level set
  have hcover : (Work.Smooth.Morse.torus ψ).carrier \ (⋃ i, Set.range (γ i).γ) =
      Work.Smooth.Morse.region ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0 ∪
        ((Work.Smooth.Morse.torus ψ).carrier ∩
          {x : R3 | 0 < Work.BoxShrink.Pinch.upperLevel s c σ u x}) := by
    rw [← hZeq, carrier_sdiff_levelSet_eq_region_union]
  have hdich := windingSpan_bot_or_top_of_inessential_boundary
    (P := Work.Smooth.Morse.torus ψ) hsimple hess hdisj hX hY hXY hcover
  -- the sublevel region of `upperLevel` is the upper region
  rw [Work.BoxShrink.Pinch.region_upperLevel] at hdich
  exact hdich

end

end Work.BoxShrink.PinchOff
