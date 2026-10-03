/-
# The remaining input of `FKSStructure`, in tree form

`Work.ORLocInd.FKSKernelCondition P` (the kernel condition for the canonical map
`⟨X | u ^ l⟩ →* ⟨X | u⟩`) is the only unproved ingredient of `FKSStructure G`, hence of
`Main.torsionFree_subgroup_locallyIndicable`.

This file reduces it to a *tree-theoretic* statement, which is the form in which the
Fischer–Karrass–Solitar structure theorem is proved: `ker π` is a free product of copies of `ℤ/l`,
so it acts on the Bass–Serre tree of that free product with **finite** vertex stabilisers and
**trivial** edge stabilisers.  Given *any* action of that kind,
`Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree` (already proved in this workspace)
finishes the job: a torsion-free subgroup meets every finite stabiliser trivially, so it acts
freely, hence is a free group, hence locally indicable.

So the only thing left to build is the tree; the group theory on top of it is done.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORLocInd.LI.isFreeGroup_locallyIndicable
import Submission.Work.ORLocInd.TF.isTorsionFree_subsingleton_of_finite
import Submission.Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree
import Submission.Work.ORBassSerre.Action.Cocompact

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

open Quiver

variable {G : Type u} [Group G]

/-- **The FKS kernel condition from an action on a tree.**

If the kernel `N = (fksQuotientHom P).ker` acts on a non-empty tree `T` without self-inverse arrows
and without inversions, with **finite** vertex stabilisers in `N` and **trivial** edge stabilisers
in `N`, then every torsion-free subgroup of `N` is free, hence locally indicable.

Indeed, let `K ≤ N` be torsion-free.  A vertex stabiliser `K ∩ N_x ≤ N_x` is finite and
torsion-free, hence trivial (`TF.isTorsionFree_subsingleton_of_finite`); every edge stabiliser is
trivial for the same reason; and `K` has no inversions, since an inverting element `g` satisfies
`g * g ∈ K ∩ N_{e.left} = 1`, so `g ^ 2 = 1`, so `g = 1` by torsion-freeness, which would make the
edge self-inverse.  So `K` acts freely and without inversions on `T`, whence `IsFreeGroup K` by
`ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree`, and `K` is locally indicable by
`LI.isFreeGroup_locallyIndicable`. -/
theorem fksKernelCondition_of_tree (P : RootPresentation G) {T : Type u} [Quiver T]
    [Quiver.HasInvolutiveReverse T] [MulAction (fksQuotientHom P).ker T]
    [Work.ORBassSerre.GraphAction (fksQuotientHom P).ker T] [Nonempty T]
    (hT : Work.ORBassSerre.IsTree T)
    (hns : ∀ e : Quiver.Total T, e.reverse ≠ e)
    (hninv : Work.ORBassSerre.ActsWithoutInversions (fksQuotientHom P).ker T)
    (hfin : ∀ x : T, Finite (MulAction.stabilizer (fksQuotientHom P).ker x))
    (hedge : ∀ e : Quiver.Total T,
      Subsingleton (MulAction.stabilizer (fksQuotientHom P).ker e)) :
    FKSKernelCondition P := by
  intro K hK
  -- `K` acts on `T` through the inclusion `K ↪ N`
  let ρ : K →* (fksQuotientHom P).ker := K.subtype
  letI : MulAction K T := MulAction.compHom T ρ
  haveI : Work.ORBassSerre.GraphAction K T :=
    { smulTotal := fun g e => Work.ORBassSerre.GraphAction.smulTotal (ρ g) e
      smulTotal_one := fun e => by
        show Work.ORBassSerre.GraphAction.smulTotal (ρ 1) e = e
        rw [map_one, Work.ORBassSerre.GraphAction.smulTotal_one]
      smulTotal_mul := fun g h e => by
        show Work.ORBassSerre.GraphAction.smulTotal (ρ (g * h)) e =
          Work.ORBassSerre.GraphAction.smulTotal (ρ g)
            (Work.ORBassSerre.GraphAction.smulTotal (ρ h) e)
        rw [map_mul, Work.ORBassSerre.GraphAction.smulTotal_mul]
      smul_left := fun g e => by
        show (Work.ORBassSerre.GraphAction.smulTotal (ρ g) e).left = g • e.left
        rw [Work.ORBassSerre.GraphAction.smul_left]
        rfl
      smul_right := fun g e => by
        show (Work.ORBassSerre.GraphAction.smulTotal (ρ g) e).right = g • e.right
        rw [Work.ORBassSerre.GraphAction.smul_right]
        rfl
      smul_reverse := fun g e => by
        show Work.ORBassSerre.GraphAction.smulTotal (ρ g) e.reverse =
          (Work.ORBassSerre.GraphAction.smulTotal (ρ g) e).reverse
        rw [Work.ORBassSerre.GraphAction.smul_reverse] }
  -- vertex stabilisers in `K` are finite and torsion-free, hence trivial
  have hstab_finite : ∀ x : T, Finite (MulAction.stabilizer K x) := fun x =>
    Finite.of_injective
      (fun y : MulAction.stabilizer K x =>
        (⟨ρ (y : K), y.2⟩ : MulAction.stabilizer (fksQuotientHom P).ker x))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (Subtype.val :
        ↥(MulAction.stabilizer (fksQuotientHom P).ker x) → ↥(fksQuotientHom P).ker) hab)))
  have hstab_subsingleton : ∀ x : T, Subsingleton (MulAction.stabilizer K x) := fun x => by
    haveI := hstab_finite x
    exact Work.ORLocInd.TF.isTorsionFree_subsingleton_of_finite
      (Work.ORLocInd.TF.isTorsionFree_of_injective (MulAction.stabilizer K x).subtype
        Subtype.val_injective hK)
  have hfree : Work.ORBassSerre.ActsFreely K T := fun g x hgx =>
    congrArg Subtype.val
      (Subsingleton.elim (⟨g, hgx⟩ : MulAction.stabilizer K x) 1)
  have hninvK : Work.ORBassSerre.ActsWithoutInversions K T := by
    intro g e he
    -- an inverting element satisfies `g * g ∈ Stab_K e.left`, which is trivial
    have hsq_fix : Work.ORBassSerre.GraphAction.smulTotal (g * g) e = e := by
      rw [Work.ORBassSerre.GraphAction.smulTotal_mul, he,
        Work.ORBassSerre.GraphAction.smul_reverse, he, Quiver.Total.reverse_reverse]
    have hmem : g * g ∈ MulAction.stabilizer K e.left := by
      rw [MulAction.mem_stabilizer_iff]
      have h1 := congrArg Quiver.Total.left hsq_fix
      rwa [Work.ORBassSerre.GraphAction.smul_left] at h1
    have hsq : g * g = 1 :=
      congrArg Subtype.val
        (Subsingleton.elim (⟨g * g, hmem⟩ : MulAction.stabilizer K e.left) 1)
    have hg : g = 1 := by
      refine hK g (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩)
      rw [pow_two]
      exact hsq
    exact hns e (by rw [← he, hg, Work.ORBassSerre.GraphAction.smulTotal_one])
  haveI : IsFreeGroup K :=
    Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree hT hfree hninvK
  exact Work.ORLocInd.LI.isFreeGroup_locallyIndicable K

end Work.ORLocInd
