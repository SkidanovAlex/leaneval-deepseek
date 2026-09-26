import Submission.Work.SurgeryInvariance.All

/-!
# Elementary facts about the winding span of a region: the empty region

The "exactly one full-rank piece" theorem (`IB/existsUnique_top_of_partition`) says that if the
surface minus a finite family of pairwise disjoint simple *inessential* closed curves is the union
of finitely many disjoint pieces open in the surface, then exactly one of the pieces has full winding
span `⊤`.  Its two-piece corollary — if one of two complementary pieces is full-rank then the other
carries no essential loop — is what turns the chapter's dichotomies (`sweep_dichotomy`,
`niceLevel_boxRegion_rank_zero_or_two`, `upperRegion_rank_zero_or_two`) from "each piece is `⊥` or
`⊤`" into a statement about *which* piece is which.

This module records the elementary input of that corollary: the empty region carries no winding.  It
is used to handle the degenerate case in which one of the two pieces of a cover is empty (there the
corollary is immediate and the exactly-one theorem, which asks all its pieces to be nonempty, does
not apply).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The empty region carries no winding.** -/
theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_eq_bot]
  rintro v ⟨γ, hγ, _⟩
  exact absurd (hγ 0) (Set.notMem_empty _)

/-- **A full-rank region is nonempty.** -/
theorem nonempty_of_windingSpan_eq_top {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (h : Work.SurgeryInvariance.WindingSpan P X = ⊤) : X.Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  rw [hcon, windingSpan_empty] at h
  exact bot_ne_top h

end

end Work.BoxShrink.PinchOff
