import Mathlib
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSF1.Cech.CechSetup

/-!
# DSG4a: the Čech nerve commutes with base change, on the level of open sets

For an algebra `A → A'`, a scheme `X` over `Spec A`, the base change
`X' = X ×_{Spec A} Spec A'` and its projection `g = baseChangeFst X f : X' ⟶ X`,
the open of `X'` attached to a simplex `x` of the Čech nerve of a family of opens
`U : ι → X.Opens` is the preimage under `g` of the corresponding open on `X`:

`Eobj (fun i => baseChangeOpen X f (U i)) n x = preimageOpen g (Eobj U n x)`.

Both sides are the product (= intersection) of the opens `U (x a)`, respectively of their
preimages, so the statement is the fact that the preimage of a finite product of opens is
the product of the preimages, recorded as `preimageOpen_prod` below.

This is the statement about the *objects* of the two Čech complexes; the comparison of the
cochain maps on top of it lives in `CechCompare.lean`.
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u v

/-- The categorical product of a finite family in a `SemilatticeInf` with `OrderTop` is the
infimum of the family.  This is `CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf`,
with the universe of the index type made independent of the universe of the lattice (which is
what the Čech nerve produces: the index type is `Fin (n+1)`, living in `Type 0`). -/
theorem piObj_eq_finset_inf {ι : Type v} {β : Type u} [SemilatticeInf β] [OrderTop β]
    [Fintype ι] (f : ι → β) : (∏ᶜ f : β) = Finset.univ.inf f := by
  trans
  · exact (IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor f))
      (CategoryTheory.Limits.CompleteLattice.finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

/-- Taking preimages under a morphism of schemes commutes with finite products of opens: the
preimage of an intersection of opens is the intersection of the preimages. -/
theorem preimageOpen_prod {X X' : Scheme.{u}} (g : X' ⟶ X) {α : Type v} [Fintype α]
    (V : α → X.Opens) :
    preimageOpen g (∏ᶜ V) = ∏ᶜ (fun a => preimageOpen g (V a)) := by
  show (TopologicalSpace.Opens.map (g : Scheme.Hom _ _).base).obj (∏ᶜ V) =
    ∏ᶜ (fun a => (TopologicalSpace.Opens.map (g : Scheme.Hom _ _).base).obj (V a))
  rw [piObj_eq_finset_inf V,
    piObj_eq_finset_inf
      (fun a => (TopologicalSpace.Opens.map (g : Scheme.Hom _ _).base).obj (V a))]
  exact map_finset_inf (f := (g : Scheme.Hom _ _).base.frameHom) Finset.univ V

theorem Eobj_baseChangeOpen {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I) :
    Work.DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U i)) n x =
      Work.DSG4a.preimageOpen (Work.DSG4a.baseChangeFst (A := A) (A' := A') X f)
        (Work.DSF1.Cech.Eobj U n x) := by
  show (∏ᶜ (fun a => Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U (x a)))) =
    Work.DSG4a.preimageOpen (Work.DSG4a.baseChangeFst (A := A) (A' := A') X f)
      (∏ᶜ (fun a => U (x a)))
  rw [preimageOpen_prod (g := Work.DSG4a.baseChangeFst (A := A) (A' := A') X f)
    (V := fun a : Fin (n + 1) => U (x a))]

end Work.DSG4a
