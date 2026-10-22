import Mathlib

import Submission.Work.ANALYTIC.CechPt.linearIndepOn_iUnion_span
import Submission.Work.ANALYTIC.CechPt.exists_linearIndepOn_span_insert
import Submission.Work.ANALYTIC.CechPt.moduleFree_of_linearIndepOn_span

/-!
# Subgroups of free abelian groups are free

This module proves that every `ℤ`-submodule of a free `ℤ`-module is free (unbounded rank).

The proof does *not* use the naive Zorn argument on pairs `(N, b)` ordered by `b ⊆ b'`: that poset
has maximal elements which are not tops (e.g. `2ℤ ≤ ℤ` with the basis `{2}`).  Instead we run Zorn
on the poset of pairs `(Y, B)`, where `Y ⊆ X` is a set of basis vectors of the ambient free module
`X →₀ ℤ` and `B` is a set-basis of the submodule `N ⊓ Finsupp.supported ℤ ℤ Y`, ordered by
`(Y ⊆ Y', B ⊆ B')`.  This poset *does* have only maximal elements at `Y = univ`:

* chains have unions as upper bounds (`IsBasisSet` is closed under directed unions);
* one step of the filtration `Y ↦ insert x Y` (with `x ∉ Y`) can be extended, because
  `(N ⊓ F_{insert x Y}) / (N ⊓ F_Y)` embeds into `ℤ` via the `x`-coordinate, hence is free, so the
  basis of `N ⊓ F_Y` extends to a basis of `N ⊓ F_{insert x Y}`.
-/

namespace Work.ANALYTIC.CechPt

/-! ### Set-bases -/

/-- A `ℤ`-*set-basis* of the submodule `A` is a linearly independent set of elements of `A` which
spans `A`.  The point of using sets rather than `Basis`es is that the index type is then fixed to
the set itself, so that the union of a chain of set-bases is again a set-basis. -/
def IsBasisSet {M : Type*} [AddCommGroup M] [Module ℤ M] (A : Submodule ℤ M) (B : Set M) : Prop :=
  LinearIndepOn ℤ id B ∧ Submodule.span ℤ B = A

/-- Every submodule of the free `ℤ`-module `X →₀ ℤ` on a type `X` is free: the Zorn argument. -/
theorem free_of_submodule_finsupp {X : Type*} (N : Submodule ℤ (X →₀ ℤ)) : Module.Free ℤ ↥N := by
  classical
  -- The poset of pairs `(Y, B)` where `B` is a set-basis of `N ⊓ Finsupp.supported ℤ ℤ Y`.
  let α := {p : Set X × Set (X →₀ ℤ) // IsBasisSet (N ⊓ Finsupp.supported ℤ ℤ p.1) p.2}
  obtain ⟨m, hm⟩ := zorn_le (α := α) (fun c hc => by
    -- The union of a chain is an upper bound.
    have hdirY : Directed (· ⊆ ·) (fun i : ↥c => ((i : α).1).1) := by
      intro i j
      rcases hc.total i.2 j.2 with hij | hji
      · exact ⟨j, (Prod.le_def.mp hij).1, subset_rfl⟩
      · exact ⟨i, subset_rfl, (Prod.le_def.mp hji).1⟩
    have hdirB : Directed (· ⊆ ·) (fun i : ↥c => ((i : α).1).2) := by
      intro i j
      rcases hc.total i.2 j.2 with hij | hji
      · exact ⟨j, (Prod.le_def.mp hij).2, subset_rfl⟩
      · exact ⟨i, subset_rfl, (Prod.le_def.mp hji).2⟩
    have hgood : IsBasisSet (N ⊓ Finsupp.supported ℤ ℤ (⋃ i : ↥c, ((i : α).1).1))
        (⋃ i : ↥c, ((i : α).1).2) :=
      linearIndepOn_iUnion_span N _ _ hdirY hdirB (fun i => (i : α).2.1)
        (fun i => (i : α).2.2)
    refine ⟨⟨(⋃ i : ↥c, ((i : α).1).1, ⋃ i : ↥c, ((i : α).1).2), hgood⟩, fun a ha => ?_⟩
    exact ⟨Set.subset_iUnion (fun i : ↥c => ((i : α).1).1) ⟨a, ha⟩,
      Set.subset_iUnion (fun i : ↥c => ((i : α).1).2) ⟨a, ha⟩⟩)
  -- At a maximal element, `Y` must be everything: otherwise one more basis vector can be added.
  have hYtop : m.1.1 = Set.univ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.ne_univ_iff_exists_notMem m.1.1 |>.mp hne
    obtain ⟨B', hle, hli', hsp'⟩ :=
      exists_linearIndepOn_span_insert N m.1.1 m.1.2 m.2.1 m.2.2 hx
    let m' : α := ⟨(insert x m.1.1, B'), hli', hsp'⟩
    have hle1 : m ≤ m' := ⟨Set.subset_insert x m.1.1, hle⟩
    have hle2 : m' ≤ m := hm hle1
    exact hx ((Prod.le_def.mp hle2).1 (Set.mem_insert x m.1.1))
  have hspN : Submodule.span ℤ m.1.2 = N := by
    rw [m.2.2, hYtop, Finsupp.supported_univ, inf_top_eq]
  exact moduleFree_of_linearIndepOn_span m.2.1 hspN

/-- Subgroups of free abelian groups are free (unbounded rank): every `ℤ`-submodule of a free
`ℤ`-module is free. Suggested route: Zorn on the poset of pairs `(N, b)` where `b` is a basis of
the submodule `N`, ordered by extending the basis (a chain with nested bases has an upper bound:
the union of the submodules is free with the union of the bases as basis, since a finite linear
relation involves only finitely many basis elements, all of them in one member of the chain). At a
maximal element `(N, b)`, if `a ∉ N` then `B + ℤa` is free: the quotient `(B+ℤa)/B` is a
subgroup of `ℤ`, hence free, so the short exact sequence splits and `B + ℤa ≅ B ⊕ ((B+ℤa)/B)`.
Alternatively, use `Module.projective` and the classical fact that projective `ℤ`-modules are
free. -/
theorem free_submodule_of_free (M : Type*) [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    (N : Submodule ℤ M) : Module.Free ℤ ↥N := by
  classical
  -- Transport along the linear equivalence `M ≃ₗ[ℤ] (X →₀ ℤ)` induced by a basis of `M`.
  let X := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis X ℤ M := Module.Free.chooseBasis ℤ M
  let e : M ≃ₗ[ℤ] (X →₀ ℤ) := b.repr
  have hfree : Module.Free ℤ ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ))) := free_of_submodule_finsupp _
  let f : ↥N → ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ))) :=
    fun n => ⟨e (n : M), Submodule.mem_map.mpr ⟨(n : M), n.2, rfl⟩⟩
  have hfval : ∀ n : ↥N, ((f n : ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ)))) : X →₀ ℤ) = e (n : M) :=
    fun _ => rfl
  have hinj : Function.Injective f := by
    intro a c h
    have h'' := congrArg (fun z : ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ))) => (z : X →₀ ℤ)) h
    rw [hfval a, hfval c] at h''
    exact Subtype.coe_injective (e.injective h'')
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, heq⟩ := Submodule.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    refine Subtype.ext ?_
    rw [hfval]
    exact heq
  let g : ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ))) → ↥N := fun y => Classical.choose (hsurj y)
  have hg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (hsurj y)
  have hgf : ∀ n, g (f n) = n := fun n => hinj (by rw [hg (f n)])
  let ee : ↥N ≃+ ↥(N.map (e : M →ₗ[ℤ] (X →₀ ℤ))) :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hg,
      map_add' := fun a c => by ext; simp [f, map_add] }
  exact Module.Free.of_equiv (ee.toIntLinearEquiv).symm

end Work.ANALYTIC.CechPt
