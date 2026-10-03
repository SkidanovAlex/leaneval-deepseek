import Mathlib
import Submission.Work.ORLocInd.RootPresentation.torsion_of_two_le
import Submission.Work.ORLocInd.Bridge.N2
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective
import Submission.Work.OROneRel.exists_root
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup

namespace Work.ORLocInd.RootPresentation

universe u

/-- **Every one-relator group either has a root presentation with nontrivial root, or is
torsion-free.**

Given a one-relator presentation `G = ⟨α | rel⟩`, extract the root `u` of `rel` (a power
`rel = u ^ l` with `u` not a proper power, `l ≥ 1`, which exists for every word by
`Work.OROneRel.exists_root`, with the degenerate case `rel = 1` handled by `u = 1`).  Then
`G ≅ ⟨α | u ^ l⟩` is a root presentation of `G`.  If `u ≠ 1` this gives the first alternative;
if `u = 1` then `rel = 1`, the presentation is the trivial one, so `G` is free on `α`, hence
torsion-free, and the second alternative holds. -/
theorem exists_rootPresentation_of_oneRelator {G : Type u} [Group G] (hG : Group.OneRelator G) :
    (∃ P : Work.ORLocInd.RootPresentation G, P.u ≠ 1) ∨ Work.ORLocInd.IsTorsionFree G := by
  obtain ⟨α, rel, ⟨e⟩⟩ := hG
  by_cases hrel : rel = 1
  · -- The trivial relator: `G ≅ ⟨α | 1⟩` is free on `α`, hence torsion-free.
    right
    have he : Work.ORLocInd.IsTorsionFree (PresentedGroup ({rel} : Set (FreeGroup α))) := by
      rw [hrel]
      exact Work.ORLocInd.isTorsionFree_presentedGroup_one
    exact Work.ORLocInd.TF.isTorsionFree_of_injective
      (e.symm : G →* PresentedGroup ({rel} : Set (FreeGroup α))) e.symm.injective he
  · -- A nontrivial relator has a root `u ≠ 1`, which is a root presentation of `G`.
    left
    obtain ⟨u, l, hl, hul, hu⟩ := Work.OROneRel.exists_root rel hrel
    -- `u` is not a proper power in the `Work.ORLocInd` sense either (that notion is weaker,
    -- since it additionally requires the root to be nontrivial).
    have hpp : ¬ Work.ORLocInd.IsProperPower u := by
      intro h
      obtain ⟨v, _, m, hm, hvm⟩ := h
      exact hu ⟨v, m, hm, hvm⟩
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, one_pow] at hul
      exact hrel hul
    refine ⟨{ α := α, u := u, l := l, one_le_l := hl,
              not_properPower := hpp, equiv := hul ▸ e }, hu1⟩

end Work.ORLocInd.RootPresentation
