/-
# The canonical input for `FKSStructure`: the torsion-free one-relator quotient `⟨X | u⟩`

`Work.ORLocInd.FKSStructure G` is the structural input of Howie's Corollary 3.2
(`Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable`): a map `π : G →* Q` onto a
torsion-free one-relator group `Q` whose kernel has the property that all of its torsion-free
subgroups are locally indicable.

This file fixes the *canonical* choice of `(Q, π)`: for a root presentation
`P : RootPresentation G` (so `G ≅ ⟨X | u ^ l⟩` with `u` not a proper power), take

* `FKSQuotient P := PresentedGroup ({P.u} : Set (FreeGroup P.α)) = ⟨X | u⟩`, and
* `fksQuotientHom P : G →* FKSQuotient P`, the quotient map.

Then `Q` is one-relator by construction, and `IsTorsionFree Q` is the Karrass–Magnus–Solitar torsion
theorem at `l = 1` (node N2's `OneRelatorCombinatorics`), recorded here as
`isTorsionFree_presentedGroup_of_not_isProperPower`.  The only remaining ingredient of
`FKSStructure G` is therefore a statement about `(fksQuotientHom P).ker` alone, which
`fksStructure_of_kernelCondition` isolates.

In the torsion-free case (`l = 1`, or more generally `IsTorsionFree G`) the input is automatic and
satisfied by `π := id` (`fksStructure_of_torsionFree`), so the kernel condition below is only needed
when `G` has torsion.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective
import Submission.Work.ORLocInd.TF.isTorsionFree_of_isMulTorsionFree
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

/-- **`FKSStructure` holds trivially for torsion-free groups**: the identity map has trivial kernel,
and a subgroup of the trivial group is locally indicable. -/
theorem fksStructure_of_torsionFree {G : Type u} [Group G] (hG : Group.OneRelator G)
    (htf : IsTorsionFree G) : FKSStructure G := by
  refine ⟨G, inferInstance, MonoidHom.id G, ?_, hG, htf⟩
  intro K _hK
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : (x : G) = 1 := by
      have hmem : (x : G) ∈ MonoidHom.ker (MonoidHom.id G) := x.2
      rwa [MonoidHom.mem_ker, MonoidHom.id_apply] at hmem
    exact Subtype.ext hx'
  subst hKbot
  intro H _ hne
  exact absurd (Subsingleton.elim H ⊥) hne

variable {G : Type u} [Group G]

/-- The **torsion-free one-relator quotient** `⟨X | u⟩` of the one-relator group `⟨X | u ^ l⟩`
presented by `P`. -/
noncomputable def FKSQuotient (P : RootPresentation G) : Type u :=
  PresentedGroup ({P.u} : Set (FreeGroup P.α))

noncomputable instance fksQuotientGroup (P : RootPresentation G) : Group (FKSQuotient P) :=
  inferInstanceAs (Group (PresentedGroup ({P.u} : Set (FreeGroup P.α))))

/-- The quotient map `⟨X | u ^ l⟩ →* ⟨X | u⟩`, transported to `G` along `P.equiv`. -/
noncomputable def fksQuotientHom (P : RootPresentation G) : G →* FKSQuotient P :=
  (PresentedGroup.toGroup
      (f := fun a : P.α => PresentedGroup.mk ({P.u} : Set (FreeGroup P.α)) (FreeGroup.of a))
      (by
        intro r hr
        rw [Set.mem_singleton_iff] at hr
        subst hr
        have hlift : FreeGroup.lift (fun a : P.α =>
            PresentedGroup.mk ({P.u} : Set (FreeGroup P.α)) (FreeGroup.of a)) =
            PresentedGroup.mk ({P.u} : Set (FreeGroup P.α)) := by
          refine MonoidHom.ext fun y => ?_
          exact (FreeGroup.lift_unique
            (f := fun a : P.α => PresentedGroup.mk ({P.u} : Set (FreeGroup P.α)) (FreeGroup.of a))
            (PresentedGroup.mk ({P.u} : Set (FreeGroup P.α))) (fun _ => rfl) (x := y)).symm
        rw [hlift, map_pow, PresentedGroup.one_of_mem (Set.mem_singleton _), one_pow])).comp
    P.equiv.symm.toMonoidHom

/-- The torsion-free quotient `⟨X | u⟩` is a one-relator group. -/
theorem fksQuotient_oneRelator (P : RootPresentation G) : Group.OneRelator (FKSQuotient P) :=
  ⟨P.α, P.u, ⟨MulEquiv.refl _⟩⟩

/-- **The Karrass--Magnus--Solitar torsion theorem at `l = 1`** (node N2's
`Work.OROneRel.kms_torsion`): if `u` is not a proper power, then `⟨X | u⟩` is torsion-free.

For `u ≠ 1`: `u` has order exactly `1` in `⟨X | u⟩`, so `u = 1` there, and every torsion element of
`⟨X | u⟩` is conjugate to a power of `u`, hence trivial.  For `u = 1` the group is free. -/
theorem isTorsionFree_presentedGroup_of_not_isProperPower {α : Type u} (u : FreeGroup α)
    (hu : ¬ IsProperPower u)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) :
    IsTorsionFree (PresentedGroup ({u} : Set (FreeGroup α))) := by
  by_cases hu1 : u = 1
  · subst hu1
    obtain ⟨e⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := α)
    exact Work.ORLocInd.TF.isTorsionFree_of_injective e.toMonoidHom e.injective
      (Work.ORLocInd.TF.isTorsionFree_of_isMulTorsionFree (G := FreeGroup α))
  · have hu' : ¬ Work.OROneRel.IsProperPower u := by
      rintro ⟨v, k, hk, hv⟩
      by_cases hv1 : v = 1
      · subst hv1
        exact hu1 (by simpa using hv)
      · exact hu ⟨v, hv1, k, hk, hv⟩
    obtain ⟨hord, htors⟩ :=
      Work.OROneRel.kms_torsion C (r := u) (u := u) (l := 1) (le_refl 1) (by rw [pow_one]) hu'
    intro g hg
    obtain ⟨k, c, hc⟩ := htors g hg
    have hu1' : PresentedGroup.mk ({u} : Set (FreeGroup α)) u = 1 := by
      rw [← orderOf_eq_one_iff]
      exact hord
    rw [hc, hu1']
    simp

/-- **The FKS kernel condition** for a root presentation `P`: every torsion-free subgroup of the
kernel of the canonical map `⟨X | u ^ l⟩ →* ⟨X | u⟩` is locally indicable.

By the Fischer–Karrass–Solitar structure theorem this kernel is a free product of copies of `ℤ/l`
(one for each conjugate of `⟨u⟩`), so a torsion-free subgroup of it is *free* by Kurosh's subgroup
theorem, hence locally indicable.  This single statement is the remaining input of `FKSStructure`
for a one-relator group with torsion; see `N4_FKS_STRUCTURE.md` for the precise analysis of what a
formalisation of it needs (the Bass–Serre tree of a free product). -/
def FKSKernelCondition (P : RootPresentation G) : Prop :=
  ∀ K : Subgroup (fksQuotientHom P).ker, IsTorsionFree K → Group.LocallyIndicable K

/-- **`FKSStructure G` from the kernel condition alone.**  For the canonical choice
`Q = ⟨X | u⟩`, `π = fksQuotientHom P`, the remaining ingredient of `FKSStructure G` is exactly
`FKSKernelCondition P`.

(`Q` is one-relator by `fksQuotient_oneRelator`, and torsion-free by
`isTorsionFree_presentedGroup_of_not_isProperPower`, which is the Karrass–Magnus–Solitar torsion
theorem at `l = 1`, an input of node N2.) -/
theorem fksStructure_of_kernelCondition (P : RootPresentation G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (hker : ∀ K : Subgroup (fksQuotientHom P).ker, IsTorsionFree K → Group.LocallyIndicable K) :
    FKSStructure G :=
  ⟨FKSQuotient P, inferInstance, fksQuotientHom P, hker, fksQuotient_oneRelator P,
    isTorsionFree_presentedGroup_of_not_isProperPower P.u P.not_properPower C⟩

end Work.ORLocInd
