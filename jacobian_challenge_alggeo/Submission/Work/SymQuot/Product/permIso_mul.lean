import Mathlib
import Submission.Work.SymQuot.Product
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Product

/-- `permIso` is a *right* action: the automorphism attached to the product `σ * τ` of
permutations is the composite of the automorphisms `τ` and `σ`, in that order. This is exactly
the convention needed for a `GAction` on the `n`-fold product. -/
theorem permIso_mul {K : Type*} [Field K] (X : Work.GCBasics.Sch K) {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    Work.SymQuot.permIso X (σ * τ) =
      (Work.SymQuot.permIso X τ).trans (Work.SymQuot.permIso X σ) := by
  apply CategoryTheory.Iso.ext
  -- Unfold both sides to the explicit `Pi.map'` morphisms attached to the two products.
  simp only [Work.SymQuot.prod, Work.SymQuot.permIso, CategoryTheory.Limits.Pi.whiskerEquiv_hom,
    CategoryTheory.Iso.trans_hom]
  -- `Pi.map'` is multiplicative in the reindexing function.
  rw [CategoryTheory.Limits.Pi.map'_comp_map']
  -- It remains to compare two `Pi.map'` morphisms along the same reindexing function
  -- `(σ * τ).symm = τ.symm ∘ σ.symm` and with pointwise-equal component morphisms.
  refine CategoryTheory.Limits.Pi.map'_eq
    (f := fun _ : Fin n => X) (g := fun _ : Fin n => X) ?_ ?_
  · funext b
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
    rfl
  · intro b
    simp only [CategoryTheory.Iso.refl_inv, CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.comp_id]

end Work.SymQuot.Product
