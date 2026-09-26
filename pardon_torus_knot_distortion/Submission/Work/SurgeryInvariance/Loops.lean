import Submission.Work.SurgeryInvariance.Core

/-!
# A sweep whose local moves are given at the level of loops

`Work.SurgeryInvariance.Sweep` records the local moves of a family of spheres through *spatial*
data (an ambient isotopy of `ℝ³` between exceptional parameters, and an embedded disc at them).
For many applications it is easier to describe the sweep directly on loops of the torus: the region
`F ∩ int(S_t)` changes only by a piece of zero winding content to which loops cannot be pinned.

This file provides that alternative interface: `SweepLoops` uses
`RegionEquivalent` (loops of one region are transported to loops of the other with the same winding
vector, in both directions) and `SurgeryStepZero` (the region gains or loses a piece of zero
winding span) instead of `RegionIsotopic` and `SurgeryShape`.  The two interfaces are related by
`RegionIsotopic.toEquivalent`, and the main theorem is the same.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- A one-parameter family of regions of `F` with finitely many `2`-surgeries, described at the
level of loops: between exceptional parameters the loop content is transported
(`RegionEquivalent`), and at an exceptional parameter the region either gains or loses a piece of
zero winding span or else is transported (`SurgeryStepZero`). -/
structure SweepLoops (P : Work.CoreTopology.ParamTorus) where
  /-- the region `F ∩ int(S_t)` -/
  region : ℝ → Set R3
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- away from the exceptional parameters the loop content is transported -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε → RegionEquivalent P (region t) (region s)
  /-- at an exceptional parameter the region changes by a piece of zero winding span -/
  surgery : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    SurgeryStepZero P (region t) (region s) ∨ RegionEquivalent P (region t) (region s)

/-- **The winding span is constant along a loop-level sweep.** -/
theorem SweepLoops.windingSpan_eq (S : SweepLoops P) (t : ℝ) :
    WindingSpan P (S.region t) = WindingSpan P (S.region 0) :=
  eq_of_locally_const (f := fun u : ℝ => WindingSpan P (S.region u)) (by
    intro u
    by_cases hu : u ∈ S.exc
    · obtain ⟨ε, hε, hshape⟩ := S.surgery u hu
      exact ⟨ε, hε, fun s hs => by
        rcases hshape s hs with h | h
        · exact h.windingSpan_eq.symm
        · exact (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h).symm⟩
    · obtain ⟨ε, hε, -, hequiv⟩ := S.regular u hu
      exact ⟨ε, hε, fun s hs =>
        (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq (hequiv s hs)).symm⟩) t 0

/-- The essential-piece invariant is constant along a loop-level sweep. -/
theorem SweepLoops.containsEssentialLoop_iff (S : SweepLoops P) (t : ℝ) :
    P.ContainsEssentialLoop (S.region t) ↔ P.ContainsEssentialLoop (S.region 0) := by
  rw [← windingSpan_ne_bot_iff P (S.region t), ← windingSpan_ne_bot_iff P (S.region 0),
    S.windingSpan_eq t]

/-- **Pardon's `spherefamily`, loop-level form.** -/
theorem SweepLoops.spherefamily (S : SweepLoops P) (h : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop (S.region 1) :=
  (S.containsEssentialLoop_iff 1).mpr h

/-- A `Sweep` gives a loop-level sweep: an ambient isotopy of `ℝ³` preserving `F` transports loops
with their winding vectors, and the geometric shape of a `2`-surgery is a change by a piece of zero
winding span. -/
def Sweep.toLoops (S : Sweep P) : SweepLoops P where
  region := S.region
  exc := S.exc
  regular t ht := by
    obtain ⟨ε, hε, hnoexc, hiso⟩ := S.regular t ht
    exact ⟨ε, hε, hnoexc, fun s hs => (hiso s hs).toEquivalent⟩
  surgery t ht := by
    obtain ⟨ε, hε, hshape⟩ := S.surgery t ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    rcases hshape s hs with h | h
    · exact Or.inl h.toZero
    · exact Or.inr h.toEquivalent

end

end Work.SurgeryInvariance
