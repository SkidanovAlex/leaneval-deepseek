import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure

universe u

namespace Work.ORHughesFree.DivisionClosure

/-- Being a division ring is invariant under ring isomorphism: `IsDivisionRing` is the
conjunction of nontriviality and "every nonzero element is a unit", both of which transport
across a ring equivalence. -/
theorem isDivisionRing_of_ringEquiv {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (h : IsDivisionRing R) : IsDivisionRing S := by
  obtain ⟨hnt, hunit⟩ := h
  have hnt' : Nontrivial R := hnt
  refine ⟨?_, ?_⟩
  · exact e.symm.toEquiv.nontrivial
  · intro x hx
    have hx' : e.symm x ≠ 0 := by
      intro h0
      apply hx
      have := congrArg e h0
      simpa using this
    simpa using (hunit (e.symm x) hx').map e

end Work.ORHughesFree.DivisionClosure
