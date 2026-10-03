import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.CoprodTree.StarTreeDefs
import Submission.Work.ORLocInd.CoprodTree.StarTreeIsTree
import Submission.Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective
import Submission.Work.ORLocInd.TF.isTorsionFree_subsingleton_of_finite

set_option linter.unusedVariables false

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre

universe u

/-! ## The Bass--Serre tree of a free product has no loops -/

/-- There is no arrow from a vertex of the star tree to itself. -/
theorem noLoop {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] (x : Vertex M) :
    ¬ Nonempty (x ⟶ x) := by
  rintro ⟨f⟩
  rcases Arrow.endpoints f with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact vtx_none_ne_vtx_some (h1.symm.trans h2)
  · exact vtx_some_ne_vtx_none (h1.symm.trans h2)

/-- No arrow of the star tree is its own reverse. -/
theorem no_self_inverse_arrow {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    (e : Quiver.Total (Vertex M)) : e.reverse ≠ e := by
  intro h
  have hlr : e.right = e.left := by
    have h1 := congrArg Quiver.Total.left h
    simpa using h1
  exact noLoop e.left ⟨hlr ▸ e.hom⟩

/-! ## The vertex stabilisers of the star tree are finite

The stabiliser of a central vertex is trivial and the stabiliser of the coset vertex
`vtx (some i) g` is the conjugate `g (M i) g⁻¹` of a finite factor of the free product
(`stabilizer_central`, `stabilizer_coset`). -/

/-- Every vertex stabiliser of the free product acting on its Bass--Serre tree is finite. -/
theorem finite_stabilizer {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] [∀ i, Finite (M i)]
    (x : Vertex M) : Finite (MulAction.stabilizer (Monoid.CoprodI M) x) := by
  obtain ⟨k, g, rfl⟩ := exists_vtx x
  match k with
  | none =>
    rw [stabilizer_central]
    exact Finite.of_surjective (fun _ : PUnit => (1 : ↥(⊥ : Subgroup (Monoid.CoprodI M))))
      (fun y => ⟨PUnit.unit, Subtype.ext (by simpa using (Subgroup.mem_bot.mp y.2).symm)⟩)
  | some i =>
    rw [stabilizer_coset]
    haveI : Finite ↥(factor M i) :=
      Finite.of_surjective (fun m : M i => (⟨Monoid.CoprodI.of m, ⟨m, rfl⟩⟩ : factor M i))
        (fun y => by obtain ⟨m, hm⟩ := y.2; exact ⟨m, Subtype.ext hm⟩)
    exact Finite.of_surjective
      (fun a : ↥(factor M i) =>
        (⟨MulEquiv.toMonoidHom (MulAut.conj g) a,
          Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩⟩ :
          ↥((factor M i).map (MulEquiv.toMonoidHom (MulAut.conj g)))))
      (fun b => by
        obtain ⟨a, ha, hb⟩ := Subgroup.mem_map.mp b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hb⟩)

/-! ## Torsion-free subgroups of groups acting on trees with finite stabilisers -/

/-- If a group `N` acts on a non-empty tree `T` without self-inverse arrows and with finite vertex
stabilisers, then every torsion-free subgroup `K ≤ N` is free.

A vertex stabiliser of `K` is a torsion-free subgroup of a finite group, hence trivial, so `K` acts
freely; and if `g ∈ K` inverts an edge `e`, then `g ^ 2` fixes its initial vertex, so `g ^ 2 = 1`,
so `g = 1`, contradicting the absence of self-inverse arrows. -/
theorem isFreeGroup_of_isTorsionFree_of_finite_stabilizers {N : Type*} {T : Type*} [Group N]
    [Quiver T] [Quiver.HasInvolutiveReverse T] [MulAction N T] [GraphAction N T] [Nonempty T]
    (hT : IsTree T) (hns : ∀ e : Quiver.Total T, e.reverse ≠ e)
    (hfin : ∀ x : T, Finite (MulAction.stabilizer N x))
    (K : Subgroup N) (hK : Work.ORLocInd.IsTorsionFree ↥K) : IsFreeGroup ↥K := by
  let ρ : K →* N := K.subtype
  letI : MulAction K T := MulAction.compHom T ρ
  haveI : GraphAction K T := graphActionSubgroup K
  -- vertex stabilisers of `K` are finite
  have hstab_finite : ∀ x : T, Finite (MulAction.stabilizer K x) := fun x => by
    haveI : Finite (MulAction.stabilizer N x) := hfin x
    refine Finite.of_injective
      (fun y : MulAction.stabilizer K x =>
        (⟨ρ (y : K), y.2⟩ : MulAction.stabilizer N x)) ?_
    intro a b hab
    have h2 : ρ (a : K) = ρ (b : K) :=
      congrArg (Subtype.val : ↥(MulAction.stabilizer N x) → N) hab
    exact Subtype.ext (Subtype.ext h2)
  -- and torsion-free, hence trivial
  have hstab_subsingleton : ∀ x : T, Subsingleton (MulAction.stabilizer K x) := fun x => by
    haveI := hstab_finite x
    exact Work.ORLocInd.TF.isTorsionFree_subsingleton_of_finite
      (Work.ORLocInd.TF.isTorsionFree_of_injective (MulAction.stabilizer K x).subtype
        Subtype.val_injective hK)
  have hfree : ActsFreely K T := fun g x hgx =>
    congrArg Subtype.val (Subsingleton.elim (⟨g, hgx⟩ : MulAction.stabilizer K x) 1)
  have hninvK : ActsWithoutInversions K T := by
    intro g e he
    have hsq_fix : GraphAction.smulTotal (g * g) e = e := by
      rw [GraphAction.smulTotal_mul, he, GraphAction.smul_reverse, he,
        Quiver.Total.reverse_reverse]
    have hmem : g * g ∈ MulAction.stabilizer K e.left := by
      rw [MulAction.mem_stabilizer_iff]
      have h1 := congrArg Quiver.Total.left hsq_fix
      rwa [GraphAction.smul_left] at h1
    have hsq : g * g = 1 :=
      congrArg Subtype.val
        (Subsingleton.elim (⟨g * g, hmem⟩ : MulAction.stabilizer K e.left) 1)
    have hg : g = 1 := by
      refine hK g (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩)
      rw [pow_two]
      exact hsq
    exact hns e (by rw [← he, hg, GraphAction.smulTotal_one])
  exact Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree hT hfree hninvK

/-! ## The main theorem: Kurosh for free products of finite groups -/

/-- A torsion-free subgroup of a free product of finite groups is free.

Note on the interface: `M` is an *explicit* argument of this statement (as requested), so it must be
supplied positionally.  At a call site with a concrete family `M`, write either

`isFreeGroup_of_isTorsionFree_subgroup M (K := K') hK'` or
`isFreeGroup_of_isTorsionFree_subgroup _ (K := K') hK'` (or use named arguments throughout,
`isFreeGroup_of_isTorsionFree_subgroup (K := K') (hK := hK')`); a bare
`isFreeGroup_of_isTorsionFree_subgroup (K := K') hK'` does not elaborate, since the positional
`hK'` would be matched against `M`.-/
theorem isFreeGroup_of_isTorsionFree_subgroup {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] [∀ i, Finite (M i)] (K : Subgroup (Monoid.CoprodI M)) (hK : Work.ORLocInd.IsTorsionFree ↥K) : IsFreeGroup ↥K := by
  haveI : Nonempty (Vertex M) := ⟨vtx none 1⟩
  exact isFreeGroup_of_isTorsionFree_of_finite_stabilizers (N := Monoid.CoprodI M)
    (T := Vertex M) starTree_isTree no_self_inverse_arrow finite_stabilizer K hK

/-- Convenience form of `isFreeGroup_of_isTorsionFree_subgroup` in which the family `M` is implicit,
so that a subgroup `K` can be passed by name: `isFreeGroup_of_isTorsionFree_subgroup' (K := K) hK`. -/
theorem isFreeGroup_of_isTorsionFree_subgroup' {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    [∀ i, Finite (M i)] (K : Subgroup (Monoid.CoprodI M)) (hK : Work.ORLocInd.IsTorsionFree ↥K) :
    IsFreeGroup ↥K :=
  isFreeGroup_of_isTorsionFree_subgroup M K hK

end Work.ORLocInd.CoprodTree
