import Mathlib
import Submission.Work.RiemLib.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CartanHadamard

/-- A covering map onto a connected base with nonempty total space is surjective.

The image of a covering map is clopen: it is open because covering maps are open maps,
and its complement is open because a point outside the image has an evenly covered
neighbourhood whose total preimage is empty.  A clopen set in a connected space is
either empty or everything, and the image is nonempty. -/
theorem surjective_of_isCoveringMap_of_connectedSpace {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] {p : Z → X} (hp : IsCoveringMap p) [ConnectedSpace X] [Nonempty Z] :
    Function.Surjective p := by
  have hcompl : IsOpen (Set.range p)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨-, U, hxU, hU, -, H, -⟩ := hp x
    have hpreU : p ⁻¹' U = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr (fun z hz => ?_)
      refine hx (Set.mem_range.mpr ⟨((H ⟨z, hz⟩).2).1, ?_⟩)
      exact Set.mem_singleton_iff.mp ((H ⟨z, hz⟩).2).2
    refine Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy hyr => ?_)
    obtain ⟨z, rfl⟩ := hyr
    have hz : z ∈ p ⁻¹' U := hy
    rw [hpreU] at hz
    exact hz
  have hclopen : IsClopen (Set.range p) :=
    ⟨IsClosed.mk hcompl, hp.isOpenMap.isOpen_range⟩
  have hne : (Set.range p).Nonempty := ⟨p (Classical.arbitrary Z), Set.mem_range_self _⟩
  rcases isClopen_iff.mp hclopen with h | h
  · rw [h] at hne
    exact (Set.not_nonempty_empty hne).elim
  · exact Set.range_eq_univ.mp h

end Work.CartanHadamard
