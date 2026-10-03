/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# Cyclically reduced conjugates of a relator

Every nontrivial element `r` of a free group is conjugate to a cyclically reduced element, and
conjugate relators present isomorphic groups.  Hence the one-relator group `⟨α | r⟩` with `r ≠ 1`
is isomorphic to `⟨α | s⟩` for some cyclically reduced nontrivial `s`.

The conjugate is read off from Mathlib's cyclic reduction of the reduced word of `r`:
`cyclicReduction r := mk (reduceCyclically r.toWord)`, with conjugating element
`cyclicConjugator r := mk (conjugator r.toWord)`.  The key input is Mathlib's
`FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically`, which says that
`conjugator L ++ reduceCyclically L ++ invRev (conjugator L) = L` as words, i.e. that
`reduceCyclically L` is conjugate to `L` in the free group.

For the presentation statement: conjugate elements generate the same normal closure, so the
quotients `FreeGroup α ⧸ normalClosure {r}` and `FreeGroup α ⧸ normalClosure {s}` — the presented
groups `⟨α | r⟩` and `⟨α | s⟩` — are isomorphic via `QuotientGroup.congr`.

## Main declarations

* `Work.OROneRel.cyclicConjugator`, `Work.OROneRel.cyclicReduction`;
* `Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv`;
* `Work.OROneRel.isCyclicallyReducedRelator_cyclicReduction`;
* `Work.OROneRel.cyclicReduction_ne_one`;
* `Work.OROneRel.presentedGroup_conj_iso`;
* `Work.OROneRel.exists_cyclicallyReduced_conjugate`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The element conjugating `cyclicReduction r` to `r`, read off from Mathlib's
`FreeGroup.reduceCyclically.conjugator`. -/
noncomputable def cyclicConjugator (r : FreeGroup α) : FreeGroup α := by
  classical exact FreeGroup.mk (FreeGroup.reduceCyclically.conjugator r.toWord)

/-- A cyclically reduced conjugate of `r`, obtained by cyclically reducing the reduced word of `r`. -/
noncomputable def cyclicReduction (r : FreeGroup α) : FreeGroup α := by
  classical exact FreeGroup.mk (FreeGroup.reduceCyclically r.toWord)

/-- `cyclicReduction r` is conjugate to `r`, with conjugating element `cyclicConjugator r`. -/
theorem cyclicConjugator_mul_cyclicReduction_mul_inv (r : FreeGroup α) :
    cyclicConjugator r * cyclicReduction r * (cyclicConjugator r)⁻¹ = r := by
  classical
  unfold cyclicConjugator cyclicReduction
  rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically]
  exact FreeGroup.mk_toWord

/-- The cyclic reduction of `r` is a cyclically reduced relator. -/
theorem isCyclicallyReducedRelator_cyclicReduction (r : FreeGroup α) :
    IsCyclicallyReducedRelator (cyclicReduction r) := by
  classical
  rw [IsCyclicallyReducedRelator, cyclicReduction, FreeGroup.toWord_mk]
  have h : FreeGroup.IsReduced (FreeGroup.reduceCyclically r.toWord) :=
    (FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord).isReduced
  rw [(FreeGroup.isReduced_iff_reduce_eq (L := FreeGroup.reduceCyclically r.toWord)).mp h]
  exact FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord

/-- The cyclic reduction of a nontrivial element is nontrivial. -/
theorem cyclicReduction_ne_one {r : FreeGroup α} (hr : r ≠ 1) : cyclicReduction r ≠ 1 := by
  intro h
  apply hr
  rw [← cyclicConjugator_mul_cyclicReduction_mul_inv r, h]
  simp

/-- Conjugate relators present isomorphic groups: if `s` is conjugate to `r`, then
`⟨α | r⟩ ≃* ⟨α | s⟩`. -/
theorem presentedGroup_conj_iso {r s : FreeGroup α} (h : IsConj r s) :
    Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      PresentedGroup ({s} : Set (FreeGroup α))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  -- Conjugate elements generate the same normal closure.
  have h1 : s ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
    have hmem : c * r * c⁻¹ ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) :=
      (Subgroup.normalClosure_normal (s := ({r} : Set (FreeGroup α)))).conj_mem r
        (Subgroup.subset_normalClosure (by simp)) c
    rwa [hc] at hmem
  have h2 : r ∈ Subgroup.normalClosure ({s} : Set (FreeGroup α)) := by
    have hmem : c⁻¹ * s * (c⁻¹)⁻¹ ∈ Subgroup.normalClosure ({s} : Set (FreeGroup α)) :=
      (Subgroup.normalClosure_normal (s := ({s} : Set (FreeGroup α)))).conj_mem s
        (Subgroup.subset_normalClosure (by simp)) c⁻¹
    have heq : c⁻¹ * s * (c⁻¹)⁻¹ = r := by rw [← hc]; group
    rwa [heq] at hmem
  have hN : Subgroup.normalClosure ({r} : Set (FreeGroup α)) =
      Subgroup.normalClosure ({s} : Set (FreeGroup α)) := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr h2)
    · exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr h1)
  refine ⟨QuotientGroup.congr _ _ (MulEquiv.refl (FreeGroup α)) ?_⟩
  rw [← hN]
  exact Subgroup.map_id _

theorem exists_cyclicallyReduced_conjugate {α : Type u} (r : FreeGroup α) (hr : r ≠ 1) :
    ∃ s : FreeGroup α, Work.OROneRel.IsCyclicallyReducedRelator s ∧ s ≠ 1 ∧
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃* PresentedGroup ({s} : Set (FreeGroup α))) := by
  refine ⟨cyclicReduction r, isCyclicallyReducedRelator_cyclicReduction r, cyclicReduction_ne_one hr,
    presentedGroup_conj_iso ?_⟩
  exact isConj_comm.mp
    (isConj_iff.mpr ⟨cyclicConjugator r, cyclicConjugator_mul_cyclicReduction_mul_inv r⟩)

end Work.OROneRel
