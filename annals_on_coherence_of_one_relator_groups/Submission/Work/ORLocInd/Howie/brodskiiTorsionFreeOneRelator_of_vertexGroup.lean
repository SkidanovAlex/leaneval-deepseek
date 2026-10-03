import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.onePresentation_exists
import Submission.Work.ORLocInd.Howie.RoseBasic
import Submission.Work.ORLocInd.FKS.hasFKSTorsionQuotient_of_freeGroup
import Submission.Work.ORLocInd.LI.isFreeGroup_locallyIndicable
import Submission.Work.ORLocInd.LI.locallyIndicable_of_injective
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.presentedGroup_pow_conj_iso
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup
import Submission.Work.OROneRel.pow_eq_one_of_relator

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

/-- Torsion-freeness is invariant under a multiplicative equivalence. -/
theorem isTorsionFree_of_mulEquiv {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    (h : Work.ORLocInd.IsTorsionFree G) : Work.ORLocInd.IsTorsionFree H := by
  intro x hx
  have hx' : IsOfFinOrder (e.symm x) := by
    rw [isOfFinOrder_iff_pow_eq_one] at hx ⊢
    obtain ⟨n, hn, hn1⟩ := hx
    exact ⟨n, hn, by rw [← map_pow, hn1, map_one]⟩
  have h1 : e.symm x = 1 := h _ hx'
  have h2 : e (e.symm x) = e 1 := by rw [h1]
  simpa using h2

/-- **A consequence of the FKS finite quotient.**  If `s = v ^ k` with `k ≥ 2` and `s ≠ 1` in a
free group, then the image of `v` in the one-relator group `⟨α | s⟩` is nontrivial (it is in fact of
order exactly `k`).

The proof uses `Work.ORLocInd.exists_finite_quotient_orderOf_eq_of_freeGroup`: `FreeGroup α` has a
finite quotient `ψ` in which the image of `v` has order exactly `k`.  Since `ψ (v ^ k) = 1`, `ψ`
factors through the presented group `⟨α | v ^ k⟩ = ⟨α | s⟩`; in that factorisation `v` maps to
`ψ v ≠ 1`, so `v` cannot be trivial in `⟨α | s⟩`. -/
theorem presentedGroup_mk_ne_one_of_isProperPower {α : Type u} {s v : FreeGroup α} {k : ℕ}
    (hs : s ≠ 1) (hk : 2 ≤ k) (hsv : s = v ^ k) :
    PresentedGroup.mk ({s} : Set (FreeGroup α)) v ≠ 1 := by
  classical
  have hv1 : v ≠ 1 := by
    intro hv
    exact hs (by rw [hsv, hv, one_pow])
  obtain ⟨Q, hQ, hFin, ψ, hψ⟩ :=
    Work.ORLocInd.exists_finite_quotient_orderOf_eq_of_freeGroup (α := α) hv1
      (by omega : 1 ≤ k)
  letI : Group Q := hQ
  letI : Finite Q := hFin
  have hψk : ψ (v ^ k) = 1 := by
    rw [map_pow, ← hψ]
    exact pow_orderOf_eq_one (ψ v)
  let f : α → Q := fun a => ψ (FreeGroup.of a)
  have hf : FreeGroup.lift f = ψ := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    simp [f, FreeGroup.lift_apply_of]
  have hrel : ∀ r ∈ ({s} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    rw [hr, hf, hsv]
    exact hψk
  let φ : PresentedGroup ({s} : Set (FreeGroup α)) →* Q :=
    PresentedGroup.toGroup (rels := {s}) (f := f) hrel
  have hφv : φ (PresentedGroup.mk ({s} : Set (FreeGroup α)) v) = ψ v := by
    rw [Work.ORLocInd.toGroup_mk (rels := {s}) (f := f) hrel v, hf]
  intro hcon
  have hψv : ψ v = 1 := by rw [← hφv, hcon, map_one]
  rw [hψv, orderOf_one] at hψ
  omega

/-- Brodskii's theorem (a torsion-free one-relator group is locally indicable) from Howie's
Theorem 3.1 in the form of a `CodeSeparates` groupoid presentation of the rose type.

Route (all ingredients are available; see `N4_LOCIND_LEAD.md` L8/L9):
  * `Group.OneRelator G` gives `α`, `rel : FreeGroup α` and `e : PresentedGroup {rel} ≃* G`;
  * if `rel = 1` then `PresentedGroup {rel} ≃* FreeGroup α` is free, hence locally indicable
    (`Work.ORLocInd.LI.isFreeGroup_locallyIndicable`);
  * otherwise use `Work.OROneRel.exists_cyclicallyReduced_conjugate` and
    `Work.OROneRel.presentedGroup_pow_conj_iso` to replace `rel` by a cyclically reduced conjugate
    `s ≠ 1` with `PresentedGroup {rel} ≃* PresentedGroup {s}`;
  * `¬ Work.OROneRel.IsProperPower s`: if `s = v ^ k`, `k ≥ 2`, `v ≠ 1`, then the (already proved,
    hypothesis-free) FKS finite quotient `Work.ORLocInd.FKS.hasFKSTorsionQuotient_of_freeGroup`
    applied to the root presentation `⟨α | v ^ k⟩` gives a finite quotient in which `v` has order
    exactly `k`, hence `v ≠ 1` in `PresentedGroup {s}` while `v ^ k = 1` there, contradicting the
    torsion-freeness of `G` (`Work.ORLocInd.FKS.isTorsionFree_ker_of_orderOf`,
    `Work.ORLocInd.FKS.ker_orderOf_eq` may help);
  * apply `h` to the `CodeSeparates` presentation produced by
    `Work.ORLocInd.Howie.onePresentation_exists` and transport local indicability along
    `Work.ORLocInd.LI.locallyIndicable_of_injective`.

`[LinearOrder α]` is chosen arbitrarily (`WellOrderingRel`) since the one-relator presentation does
not depend on it.  The caller instantiates `h` with
`Work.ORLocInd.Howie.locallyIndicable_vertexGroup_codeSeparates` (`Howie/theorem31.lean`). -/
theorem brodskiiTorsionFreeOneRelator_of_vertexGroup
    (h : ∀ {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
      (P : Work.ORLocInd.Howie.Presentation V) (v : V),
      P.CodeSeparates → Work.ORLocInd.Group.LocallyIndicable (P.vertexGroup v)) :
    Work.ORLocInd.BrodskiiTorsionFreeOneRelator.{u} := by
  refine ⟨?_⟩
  intro G _instG hG hTF
  obtain ⟨α, rel, ⟨e⟩⟩ := hG
  classical
  by_cases hrel : rel = 1
  · subst hrel
    obtain ⟨e0⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := α)
    have hLI : Work.ORLocInd.Group.LocallyIndicable (FreeGroup α) :=
      Work.ORLocInd.LI.isFreeGroup_locallyIndicable (FreeGroup α)
    exact Work.ORLocInd.LI.locallyIndicable_of_injective
      ((e.symm.trans e0 : G ≃* FreeGroup α) : G →* FreeGroup α)
      (e.symm.trans e0).injective hLI
  · obtain ⟨s, hcyc, hs1, ⟨e'⟩⟩ := Work.OROneRel.exists_cyclicallyReduced_conjugate rel hrel
    have hpp : ¬ Work.OROneRel.IsProperPower s := by
      rintro ⟨v, k, hk, hsv⟩
      have hmk : PresentedGroup.mk ({s} : Set (FreeGroup α)) v ≠ 1 :=
        presentedGroup_mk_ne_one_of_isProperPower hs1 hk hsv
      have hpow : (PresentedGroup.mk ({s} : Set (FreeGroup α)) v) ^ k = 1 :=
        Work.OROneRel.pow_eq_one_of_relator s v k hsv
      have hfin : IsOfFinOrder (PresentedGroup.mk ({s} : Set (FreeGroup α)) v) :=
        isOfFinOrder_iff_pow_eq_one.mpr ⟨k, by omega, hpow⟩
      have hTFs : Work.ORLocInd.IsTorsionFree (PresentedGroup ({s} : Set (FreeGroup α))) :=
        isTorsionFree_of_mulEquiv (e.symm.trans e') hTF
      exact hmk (hTFs _ hfin)
    letI : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
    obtain ⟨P, hsep, ⟨eP⟩⟩ :=
      Work.ORLocInd.Howie.onePresentation_exists s hcyc hs1 hpp
    have hLIvg : Work.ORLocInd.Group.LocallyIndicable (P.vertexGroup (roseVtx α)) :=
      h P (roseVtx α) hsep
    exact Work.ORLocInd.LI.locallyIndicable_of_injective
      (((e.symm.trans e').trans eP.symm : G ≃* P.vertexGroup (roseVtx α)) : G →* _)
      (((e.symm.trans e').trans eP.symm).injective) hLIvg

end Work.ORLocInd.Howie
