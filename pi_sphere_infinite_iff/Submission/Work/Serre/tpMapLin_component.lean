import Mathlib
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The components of the tensor product of two chain maps

`Work.Kunneth.tpMapLin C C' D D' f g n` is the `n`-th component of the tensor product of two
chain maps `f : C ⟶ C'`, `g : D ⟶ D'` on the Koszul tensor product
(`Submission/Work/Kunneth/EZAWTensor.lean`).  By definition it is the `DirectSum.toModule`
packaging of the summand maps

`(p,q) ↦ tpLof (p,q) ∘ (f_p ⊗ g_q) : C_p ⊗ D_q ⟶ ⨁_{r+s=n} C'_r ⊗ D'_s`,

and this file records the resulting **component formula**: the `(p,q)`-component of
`tpMapLin C C' D D' f g n x` is obtained by applying `f_p ⊗ g_q` to the `(p,q)`-component of `x`
(and forgetting the other components of `x` entirely):

`(tpMapLin C C' D D' f g n x) pq = (f_p ⊗ g_q) (x pq)`.

The proof is the general observation that a `DirectSum.toModule` whose summand maps all factor
through the corresponding `lof`s is exactly the `DirectSum.lmap` of those maps, whose component
formula is `DirectSum.lmap_apply`.

## A note on instances

As in the rest of the `Work.Kunneth` chapter (and as in `Submission/Work/Serre/tpDApplyComp.lean`),
the generic `AddCommGroup.toIntModule` instance is removed, so that typeclass search picks the
scalar structures (`TensorProduct.instModule`, `ModuleCat.isModule`, `DirectSum.instModule`) that
the definitions of that chapter were elaborated with.  This only changes which of several
propositionally (indeed definitionally) equal instances is found while *proving*; the statement of
`Work.Serre.tpMapLin_component` below is definitionally identical with and without that line.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct
open Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- A `DirectSum.toModule` whose `i`-th summand map is `lof i ∘ₗ φ i` is the `DirectSum.lmap`
of the family `φ`. -/
private lemma toModule_lof_eq_lmap {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]
    (φ : ∀ i, M i →ₗ[ℤ] N i) :
    DirectSum.toModule ℤ ι (DirectSum ι N) (fun j => DirectSum.lof ℤ ι N j ∘ₗ φ j)
      = DirectSum.lmap φ := by
  refine DirectSum.linearMap_ext ℤ (fun j => ?_)
  ext a
  simp [DirectSum.lmap_lof, DirectSum.toModule_lof]

theorem tpMapLin_component (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) (pq : Work.Kunneth.tpIdx n) (x : Work.Kunneth.tpX C D n) :
    DirectSum.component ℤ (Work.Kunneth.tpIdx n)
        (fun rs => Work.Kunneth.tpSummand C' D' rs.1.1 rs.1.2) pq
        (Work.Kunneth.tpMapLin C C' D D' f g n x)
      = TensorProduct.map (f.f pq.1.1).hom (g.f pq.1.2).hom
          (DirectSum.component ℤ (Work.Kunneth.tpIdx n)
            (fun rs => Work.Kunneth.tpSummand C D rs.1.1 rs.1.2) pq x) := by
  have hmap : Work.Kunneth.tpMapLin C C' D D' f g n
      = DirectSum.lmap (fun rs : Work.Kunneth.tpIdx n =>
            TensorProduct.map (f.f rs.1.1).hom (g.f rs.1.2).hom) := by
    rw [Work.Kunneth.tpMapLin]
    exact toModule_lof_eq_lmap _
  rw [hmap]
  exact DirectSum.lmap_apply
    (f := fun rs : Work.Kunneth.tpIdx n =>
      TensorProduct.map (f.f rs.1.1).hom (g.f rs.1.2).hom) x pq

end

end Work.Serre
