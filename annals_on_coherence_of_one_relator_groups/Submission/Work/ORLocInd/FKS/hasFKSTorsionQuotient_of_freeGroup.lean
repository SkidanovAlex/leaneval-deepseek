/-
# The FKS finite quotient, from Hall's theorem alone

The Fischer--Karrass--Solitar finite quotient for a root presentation `⟨X | u ^ l⟩` is, in the form
needed by node N4, a *free group* statement: for every `n ≥ 1` and every nontrivial `u` in a finitely
generated free group `F`, there is a finite quotient `Q` of `F` in which the image of `u` has order
exactly `n` (FKS 1972, Theorem 2).  The point of the statement is that the quotient can be taken
*finite*, which is what makes the kernel of the induced map `G → Q` a finite-index torsion-free
subgroup, by the Karrass--Magnus--Solitar torsion theorem.

The present module assembles the two ingredients of that free-group statement into the
`HasFKSTorsionQuotient` of a root presentation of an arbitrary (possibly infinitely generated)
one-relator group:

* `Work.ORLocInd.ResiduallyFinitePGroup` (P. Hall 1950: free groups are residually finite
  `p`-groups) and the finite-`p`-group order reduction
  (`Work.ORLocInd.FKS.exists_finite_pGroup_quotient_orderOf_eq`) give the finitely generated case
  (`Work.ORLocInd.FKS.exists_finiteGroup_hom_orderOf_eq`);
* `Work.ORLocInd.FKS.exists_finite_retraction_nontrivial` reduces an arbitrary element of a free
  group on an arbitrary generating type to the finitely generated case;
* the quotient of the free group descends to the presented group `⟨X | u ^ l⟩`, since the image of
  `u` has order dividing `l`.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Hall.Basic
import Submission.Work.ORLocInd.Hall.exists_finite_pGroup_hom_ne_one_of_finset
import Submission.Work.ORLocInd.FKS.exists_finite_retraction_nontrivial
import Submission.Work.ORLocInd.FKS.exists_finiteGroup_hom_orderOf_eq
import Submission.Work.ORLocInd.FKS.freeGroup_separated_by_finite_p_group

set_option autoImplicit false

universe u

namespace Work.ORLocInd

/-- The composite of the canonical map `FreeGroup α →* PresentedGroup rels` with `toGroup` is the
lift of `f`: `toGroup h (mk rels v) = FreeGroup.lift f v`. -/
theorem toGroup_mk {α : Type*} {G : Type*} [Group G] {rels : Set (FreeGroup α)} {f : α → G}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (v : FreeGroup α) :
    PresentedGroup.toGroup (rels := rels) (f := f) h (PresentedGroup.mk rels v)
      = FreeGroup.lift f v := by
  have hcomp : (PresentedGroup.toGroup (rels := rels) (f := f) h).comp (PresentedGroup.mk rels)
      = FreeGroup.lift f := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    have h1 : (PresentedGroup.mk rels) (FreeGroup.of x) = PresentedGroup.of x := rfl
    rw [MonoidHom.comp_apply, h1, PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]
  exact congrArg (fun g : FreeGroup α →* G => g v) hcomp

/-- **P. Hall (1950) for finitely generated free groups**, in the form used here: the free group on a
finite type is residually a finite `p`-group. -/
theorem residuallyFinitePGroup_of_fintype {α : Type u} [Fintype α] :
    ResiduallyFinitePGroup α :=
  fun p hp w hw => FKS.freeGroup_separated_by_finite_p_group (α := α) hp w hw

/-- **Fischer--Karrass--Solitar 1972, Theorem 2, for an arbitrary free group**: if `u ≠ 1` in the
free group on `α`, and `1 ≤ n`, then some *finite* quotient of `FreeGroup α` has the image of `u` of
order exactly `n`.  (Reduction to the finitely generated case by
`Work.ORLocInd.FKS.exists_finite_retraction_nontrivial`.) -/
theorem exists_finite_quotient_orderOf_eq_of_freeGroup {α : Type u} {u : FreeGroup α} (hu : u ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (ψ : FreeGroup α →* Q), orderOf (ψ u) = n := by
  obtain ⟨S, ρ, hρ⟩ := FKS.exists_finite_retraction_nontrivial (α := α) hu
  haveI : Fintype ↥S := S.fintypeCoeSort
  obtain ⟨Q, hQ, hFin, ψ, hψ⟩ :=
    FKS.exists_finiteGroup_hom_orderOf_eq (residuallyFinitePGroup_of_fintype (α := ↥S)) hρ hn
  exact ⟨Q, hQ, hFin, ψ.comp ρ, by rw [MonoidHom.comp_apply]; exact hψ⟩

/-- **The FKS finite quotient of a root presentation with nontrivial root.**  If `P` is a root
presentation `⟨X | u ^ l⟩` of `G` with `u ≠ 1` in the free group, then `G` has a finite quotient in
which the root element has order exactly `l`. -/
theorem hasFKSTorsionQuotient_of_freeGroup {G : Type u} [Group G] (P : RootPresentation G)
    (hu : P.u ≠ 1) : HasFKSTorsionQuotient P := by
  obtain ⟨S, ρ, hρ⟩ := FKS.exists_finite_retraction_nontrivial (α := P.α) hu
  haveI : Fintype ↥S := S.fintypeCoeSort
  obtain ⟨Q, hQ, hFin, ψ, hψ⟩ :=
    FKS.exists_finiteGroup_hom_orderOf_eq (residuallyFinitePGroup_of_fintype (α := ↥S)) hρ P.one_le_l
  letI : Group Q := hQ
  letI : Finite Q := hFin
  let Ψ : FreeGroup P.α →* Q := ψ.comp ρ
  have hΨ : orderOf (Ψ P.u) = P.l := hψ
  have hrel : Ψ (P.u ^ P.l) = 1 := by
    rw [map_pow]
    exact (by rw [← hΨ]; exact pow_orderOf_eq_one (Ψ P.u))
  let f : P.α → Q := fun a => Ψ (FreeGroup.of a)
  have hf : FreeGroup.lift f = Ψ := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    simp [f, FreeGroup.lift_apply_of]
  have hh : ∀ r ∈ ({P.u ^ P.l} : Set (FreeGroup P.α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [hf]
    exact hrel
  let φ : G →* Q := (PresentedGroup.toGroup (rels := {P.u ^ P.l}) (f := f) hh).comp
    (P.equiv.symm : G →* PresentedGroup ({P.u ^ P.l} : Set (FreeGroup P.α)))
  have hroot : φ P.rootElem = Ψ P.u := by
    show PresentedGroup.toGroup (rels := {P.u ^ P.l}) (f := f) hh
      (P.equiv.symm (P.rootElem)) = Ψ P.u
    rw [RootPresentation.rootElem, MulEquiv.symm_apply_apply]
    rw [toGroup_mk hh P.u, hf]
  exact ⟨Q, hQ, hFin, φ, by rw [hroot, hΨ]⟩

end Work.ORLocInd
