import Mathlib
import Submission.Work.BoxShrink.PinchOff.Extras
import Submission.Work.BoxShrink.Pinch.Level

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

-- Pardon's equation (1) (`Work.BoxShrink.Pinch.Equation1Input`), for the smooth tori of the
-- challenge: for a *nice* level set of a continuous function (a finite disjoint union of simple
-- closed curves of the surface) which carries no essential loop, the sublevel region
-- `region ψ g t = F ∩ {g < t}` has winding span `⊥` or `⊤` (`PardonDichotomy`).
--
-- This is a carried classical input of the parent chapter (`Work.BoxShrink.Pinch.Level.lean`), and
-- it follows from the *proved* dichotomy engine of this directory:
-- `Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary`, applied to
--   * the finite family of circles of `NiceLevel.circleUnion` (simple, pairwise disjoint, each
--     inessential because the level set carries no essential loop),
--   * `X = region ψ g t`, `Y = F ∩ {t < g}` — both open in the carrier since `g` is continuous,
--     disjoint, with `F \ levelSet = X ∪ Y` by trichotomy of `<` on the values of `g`.
theorem equation1Input_holds : Work.BoxShrink.Pinch.Equation1Input := by
  intro ψ g t hg hnice hiness
  obtain ⟨n, γ, hsimple, hdisj, hUnion⟩ := hnice.circleUnion
  refine windingSpan_bot_or_top_of_inessential_boundary
    (P := Work.Smooth.Morse.torus ψ)
    (X := Work.Smooth.Morse.region ψ g t)
    (Y := (Work.Smooth.Morse.torus ψ).carrier ∩ {x : R3 | t < g x})
    (n := n) (γ := γ) hsimple ?_ hdisj ?_ ?_ ?_ ?_
  · -- each circle of the level set is inessential: it would otherwise exhibit an essential loop
    -- carried by the level set
    intro i hess
    exact hiness ⟨γ i, hess, fun s => by
      rw [hUnion]
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self s⟩⟩
  · -- `region ψ g t = F ∩ {g < t}` is open in the carrier
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := Work.Smooth.Morse.torus ψ)
      (isOpen_lt hg continuous_const)
  · -- `F ∩ {t < g}` is open in the carrier
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := Work.Smooth.Morse.torus ψ)
      (isOpen_lt continuous_const hg)
  · -- the two regions are disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Work.Smooth.Morse.mem_region] at hx
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
    exact absurd hx.2 (not_lt.mpr hy.2.le)
  · -- `F \ levelSet = X ∪ Y`
    rw [← hUnion]
    ext x
    constructor
    · rintro ⟨hx, hxt⟩
      have hne : g x ≠ t := fun h => hxt (by
        rw [Work.Smooth.Morse.mem_levelSet]; exact ⟨hx, h⟩)
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · refine ⟨hx, ?_⟩
        rw [Work.Smooth.Morse.mem_levelSet]
        rintro ⟨-, hgt⟩
        exact (ne_of_lt h) hgt
      · refine ⟨hx, ?_⟩
        rw [Work.Smooth.Morse.mem_levelSet]
        rintro ⟨-, hgt⟩
        exact (ne_of_gt h) hgt

end Work.BoxShrink.PinchOff
