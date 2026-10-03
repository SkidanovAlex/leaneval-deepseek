import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.CoprodTree.isFreeGroup_of_isTorsionFree_subgroup
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective

namespace Work.ORLocInd.CoprodTree

universe u v

/-!
# Kurosh for free products of finite groups, without a universe restriction

`isFreeGroup_of_isTorsionFree_subgroup` proves that a torsion-free subgroup of a free product of
finite groups is free, but only when the index type `ι` and the factors `M i` live in the *same*
universe.  The application in `Submission/Work/ORLocInd/FKSKernelCondition.lean` needs the general
case: there the index type sits in a universe `u` while the factors are finite groups such as
`ZMod l`, which live in a smaller universe `v`.

The gap is bridged by transporting along a group isomorphism.  Moving both the index type and every
factor to the common universe `max u v` produces a family `coprodIULiftFamily M` to which the
existing theorem applies, and the universal property of the free product yields an isomorphism
`coprodIULiftEquiv : Monoid.CoprodI M ≃* Monoid.CoprodI (coprodIULiftFamily M)`.  Free groups, and
torsion-free groups, are both preserved by such an isomorphism, so the conclusion can be pulled
back to `K`.
-/

/-! ## Lifting a free product to a common universe -/

/-- The family of groups obtained from `M : ι → Type v` (`ι : Type u`) by moving both the index
type and every factor to the common universe `max u v`.

Both the index type `ULift.{max u v, u} ι` and the factors `ULift.{max u v, v} (M i)` are types in
`Type (max u v)`, so `Monoid.CoprodI (coprodIULiftFamily M)` is a free product whose index type and
factors live in one universe, which is the shape required by
`isFreeGroup_of_isTorsionFree_subgroup`. -/
abbrev coprodIULiftFamily {ι : Type u} (M : ι → Type v) :
    ULift.{max u v, u} ι → Type (max u v) :=
  fun j => ULift.{max u v, v} (M j.down)

section Equiv

variable {ι : Type u} {M : ι → Type v} [∀ i, Group (M i)]

/-- The canonical map `∗ᵢ M i →* ∗ⱼ coprodIULiftFamily M j` on the free products, sending the
copy of `M i` in the source to the copy of `ULift (M i)` in the target by `ULift.up`. -/
noncomputable def coprodIULiftToHom : Monoid.CoprodI M →*
    Monoid.CoprodI (coprodIULiftFamily M) :=
  Monoid.CoprodI.lift (M := M) (N := Monoid.CoprodI (coprodIULiftFamily M))
    (fun i : ι =>
      (Monoid.CoprodI.of (M := coprodIULiftFamily M) (i := ULift.up i)).comp
        (MulEquiv.ulift.symm.toMonoidHom))

/-- The inverse of `coprodIULiftToHom`, induced by `ULift.down` on each factor. -/
noncomputable def coprodIULiftInvHom : Monoid.CoprodI (coprodIULiftFamily M) →*
    Monoid.CoprodI M :=
  Monoid.CoprodI.lift (M := coprodIULiftFamily M) (N := Monoid.CoprodI M)
    (fun j : ULift.{max u v, u} ι =>
      (Monoid.CoprodI.of (M := M) (i := j.down)).comp (MulEquiv.ulift.toMonoidHom))

/-- **The free product is unchanged when the index type and the factors are lifted to a common
universe.**  This is the isomorphism induced by `ULift.up` on the free generators; it witnesses that
`Monoid.CoprodI M` and `Monoid.CoprodI (coprodIULiftFamily M)` are the same group presented with
the factors living in different universes. -/
noncomputable def coprodIULiftEquiv : Monoid.CoprodI M ≃*
    Monoid.CoprodI (coprodIULiftFamily M) :=
  MonoidHom.toMulEquiv coprodIULiftToHom coprodIULiftInvHom (by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext m
    simp [coprodIULiftToHom, coprodIULiftInvHom, MonoidHom.comp_apply]) (by
    apply Monoid.CoprodI.ext_hom
    intro j
    ext x
    cases x with
    | up m => simp [coprodIULiftToHom, coprodIULiftInvHom, MonoidHom.comp_apply])

end Equiv

/-! ## Free groups are preserved by isomorphisms -/

/-- Freedom is an isomorphism invariant: pushing a free group basis through a group isomorphism
(`FreeGroupBasis.map`) gives a free group basis of the target. -/
lemma isFreeGroup_of_mulEquiv {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    (h : IsFreeGroup G) : IsFreeGroup H :=
  let ⟨ι, ⟨b⟩⟩ := h.nonempty_basis
  ⟨ι, ⟨b.map e⟩⟩

/-! ## The main theorem -/

/-- A torsion-free subgroup of a free product of finite groups is free.  This is
`isFreeGroup_of_isTorsionFree_subgroup` without the restriction that the index type `ι` and the
factors `M i` lie in the same universe: the free product is transported, along
`coprodIULiftEquiv`, to the free product `Monoid.CoprodI (coprodIULiftFamily M)` of the lifted
family, whose index type and factors both live in `Type (max u v)`. -/
theorem isFreeGroup_of_isTorsionFree_subgroup_univ {ι : Type u} {M : ι → Type v} [∀ i, Group (M i)] [∀ i, Finite (M i)] (K : Subgroup (Monoid.CoprodI M)) (hK : Work.ORLocInd.IsTorsionFree ↥K) : IsFreeGroup ↥K := by
  have hfin : ∀ j : ULift.{max u v, u} ι, Finite (coprodIULiftFamily M j) :=
    fun j => inferInstance
  let K' : Subgroup (Monoid.CoprodI (coprodIULiftFamily M)) :=
    K.map (coprodIULiftEquiv (M := M)).toMonoidHom
  -- `K'` is torsion-free, being isomorphic to `K`
  have hK' : Work.ORLocInd.IsTorsionFree ↥K' :=
    Work.ORLocInd.TF.isTorsionFree_of_injective
      (((coprodIULiftEquiv (M := M)).subgroupMap K).symm).toMonoidHom
      ((coprodIULiftEquiv (M := M)).subgroupMap K).symm.injective hK
  -- hence `K'` is free, and freedom transfers back along the isomorphism `↥K ≃* ↥K'`
  have hfree : IsFreeGroup ↥K' :=
    isFreeGroup_of_isTorsionFree_subgroup (M := coprodIULiftFamily M) K' hK'
  exact isFreeGroup_of_mulEquiv ((coprodIULiftEquiv (M := M)).subgroupMap K).symm hfree

end Work.ORLocInd.CoprodTree
