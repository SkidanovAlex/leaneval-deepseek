/-
# Node N2 → node N4: the Karrass--Magnus--Solitar bridge

Node N2 (`Work.OROneRel`) exports the four classical theorems of one-relator group theory bundled
in the `Prop`-valued structure `Work.OROneRel.OneRelatorCombinatorics`.  Its `kms_torsion` field is
verbatim the Magnus--Karrass--Solitar torsion theorem: if `r = u ^ l` with `l ≥ 1` and `u` not a
proper power, then `u` has order exactly `l` in `⟨α | r⟩` and every element of finite order is
conjugate to a power of `u`.

This file is the bridge: it turns that statement into the `TorsionTheory` of the root presentation
`⟨α | u ^ l⟩` developed in `Work.ORLocInd.Basic`, and hence produces the main theorem of node N4
(virtual torsion-freeness) with the KMS input discharged.  The only remaining literature input for
virtual torsion-freeness is then the Fischer--Karrass--Solitar finite quotient, which enters as an
explicit hypothesis `HasFKSTorsionQuotient`.

Note on conventions: the two nodes use slightly different (but equivalent on nontrivial words)
notions of "proper power":

* `Work.ORLocInd.IsProperPower w := ∃ v ≠ 1, ∃ m, 2 ≤ m ∧ w = v ^ m` (the trivial word is *not* a
  proper power, so that a free group can be presented as `⟨α | 1 ^ 1⟩`);
* `Work.OROneRel.IsProperPower r := ∃ u, ∃ k, 2 ≤ k ∧ r = u ^ k`.

The two conversion lemmas below move between them.
-/
import Submission.Work.ORLocInd.Core
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

set_option autoImplicit false

universe u

namespace Work.ORLocInd

variable {α : Type u}

section ProperPower

/-- The `Work.ORLocInd` notion of proper power implies the `Work.OROneRel` one. -/
theorem orOneRel_isProperPower_of_isProperPower {w : FreeGroup α} (h : IsProperPower w) :
    Work.OROneRel.IsProperPower w := by
  obtain ⟨v, _, m, hm, rfl⟩ := h
  exact ⟨v, m, hm, rfl⟩

/-- For a nontrivial word, the `Work.OROneRel` notion of proper power implies the
`Work.ORLocInd` one. -/
theorem isProperPower_of_orOneRel_isProperPower {w : FreeGroup α} (hw : w ≠ 1)
    (h : Work.OROneRel.IsProperPower w) : IsProperPower w := by
  obtain ⟨v, m, hm, rfl⟩ := h
  refine ⟨v, ?_, m, hm, rfl⟩
  intro hv
  exact hw (by rw [hv]; exact one_pow m)

end ProperPower



section RootPresentation

/-- **Node N2 → node N4 (KMS).**  The Karrass--Magnus--Solitar torsion theorem, in the form in which
node N4 consumes it: the root presentation `⟨α | u ^ l⟩` of a one-relator group satisfies
`TorsionTheory`. -/
theorem torsionTheory_of_kms (C : Work.OROneRel.OneRelatorCombinatorics.{u}) {α : Type u}
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (hu : ¬ IsProperPower u) (hu1 : u ≠ 1) :
    TorsionTheory (rootPresentation u l hl hu) := by
  have hu' : ¬ Work.OROneRel.IsProperPower u :=
    fun h => hu (isProperPower_of_orOneRel_isProperPower hu1 h)
  have h := C.kms_torsion (α := α) (r := u ^ l) (u := u) (l := l) hl rfl hu'
  refine ⟨?_, ?_⟩
  · rw [rootPresentation_rootElem]; exact h.1
  · intro g hg
    obtain ⟨k, c, hc⟩ := h.2 g hg
    exact ⟨k, c, by rw [rootPresentation_rootElem]; exact hc⟩

end RootPresentation

section FreeCase

/-- The trivial-relator presentation `⟨α | 1⟩` is the free group on `α`, hence torsion-free. -/
theorem isTorsionFree_presentedGroup_one :
    IsTorsionFree (PresentedGroup ({1} : Set (FreeGroup α))) := by
  obtain ⟨e⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := α)
  exact IsTorsionFree.of_injective (e : PresentedGroup ({1} : Set (FreeGroup α)) →* FreeGroup α)
    e.injective (IsTorsionFree.of_isMulTorsionFree (G := FreeGroup α))

/-- The trivial-relator presentation `⟨α | 1⟩` is virtually torsion-free. -/
theorem virtuallyTorsionFree_presentedGroup_one :
    VirtuallyTorsionFree (PresentedGroup ({1} : Set (FreeGroup α))) :=
  VirtuallyTorsionFree.of_finiteIndex
    ⟨⊤, inferInstance, IsTorsionFree.top isTorsionFree_presentedGroup_one⟩

end FreeCase

section Main

/-- **Theorem 1 of node N4, with the KMS input discharged by node N2.**  Let `r = u ^ l` with
`l ≥ 1` and `u` not a proper power.  If the one-relator group `⟨α | u ^ l⟩` has a finite quotient in
which the image of `u` has order exactly `l` (Fischer--Karrass--Solitar), then it is virtually
torsion-free. -/
theorem virtuallyTorsionFree_of_kms_of_fks (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (hu : ¬ IsProperPower u)
    (hFKS : HasFKSTorsionQuotient (rootPresentation u l hl hu)) :
    VirtuallyTorsionFree (PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
  rcases eq_or_ne u 1 with rfl | hu1
  · have hset : ({1 ^ l} : Set (FreeGroup α)) = {1} := by ext x; simp
    rw [hset]
    exact virtuallyTorsionFree_presentedGroup_one
  · exact virtuallyTorsionFree_of_hasTorsionInput
      ⟨rootPresentation u l hl hu, torsionTheory_of_kms C u l hl hu hu1, hFKS⟩

/-- **Theorem 1 of node N4, in its most usable form.**  Let `P` be a root presentation of `G`
(`G ≅ ⟨X | u ^ l⟩` with `u` not a proper power, `1 ≤ l`).  If `G` has a finite quotient in which
the image of the root has order exactly `l`, then `G` is virtually torsion-free.  The
Magnus--Karrass--Solitar half of the input is discharged by node N2; only the
Fischer--Karrass--Solitar finite quotient remains a hypothesis. -/
theorem virtuallyTorsionFree_of_kms_of_fks_rootPresentation
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) {G : Type u} [Group G]
    (P : RootPresentation G) (hFKS : HasFKSTorsionQuotient P) : VirtuallyTorsionFree G := by
  by_cases hu1 : P.u = 1
  · -- trivial root: the group is presented by the empty relator, hence free
    have hset : ({1 ^ P.l} : Set (FreeGroup P.α)) = {1} := by ext x; simp
    have hv : VirtuallyTorsionFree (PresentedGroup ({P.u ^ P.l} : Set (FreeGroup P.α))) := by
      rw [hu1, hset]
      exact virtuallyTorsionFree_presentedGroup_one
    exact VirtuallyTorsionFree.of_mulEquiv P.equiv hv
  · -- nontrivial root: node N2's KMS applies
    have hKMS : TorsionTheory (rootPresentation P.u P.l P.one_le_l P.not_properPower) :=
      torsionTheory_of_kms C P.u P.l P.one_le_l P.not_properPower hu1
    have hFKS' : HasFKSTorsionQuotient (rootPresentation P.u P.l P.one_le_l P.not_properPower) := by
      obtain ⟨Q, hQ, hQfin, φ, hφ⟩ := hFKS
      refine ⟨Q, hQ, hQfin,
        φ.comp (P.equiv : PresentedGroup ({P.u ^ P.l} : Set (FreeGroup P.α)) →* G), ?_⟩
      show orderOf (φ (P.equiv (PresentedGroup.mk ({P.u ^ P.l} : Set (FreeGroup P.α)) P.u))) = P.l
      exact hφ
    have hv : VirtuallyTorsionFree (PresentedGroup ({P.u ^ P.l} : Set (FreeGroup P.α))) :=
      virtuallyTorsionFree_of_hasTorsionInput
        ⟨rootPresentation P.u P.l P.one_le_l P.not_properPower, hKMS, hFKS'⟩
    exact VirtuallyTorsionFree.of_mulEquiv P.equiv hv

/-- **The output of node N4 in the form consumed by nodes N6/N10.**  For a one-relator group with a
root presentation `P` and the FKS finite quotient, and with Brodskii's theorem available, there is a
normal finite-index subgroup that is torsion-free and locally indicable. -/
theorem exists_normal_finiteIndex_torsionFree_locallyIndicable_of_kms_of_fks
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) {G : Type u} [Group G]
    (P : RootPresentation G) (hb : BrodskiiHowieInput G) (hFKS : HasFKSTorsionQuotient P) :
    ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G' ∧ Group.LocallyIndicable G' := by
  obtain ⟨G', hN, hfi, htf⟩ := virtuallyTorsionFree_of_kms_of_fks_rootPresentation C P hFKS
  exact ⟨G', hN, hfi, htf, hb G' htf⟩

end Main

end Work.ORLocInd
