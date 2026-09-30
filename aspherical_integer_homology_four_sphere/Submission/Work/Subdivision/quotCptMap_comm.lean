/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataCpt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The quotient map commutes with the differential

For `f : C ⟶ C'` a morphism of chain complexes of `ℤ`-modules and subcomplex
data `S ⊆ C`, `S' ⊆ C'` satisfying `S k ≤ (S' k).comap (f.f k).hom`, the
degreewise maps `S.quotCptMap S' f hf k : S.quot.X k ⟶ S'.quot.X k` (which are
`Submodule.mapQ` on the quotients, promoted to `ModuleCat ℤ`) form a morphism of
complexes: they commute with the induced differentials `SubData.quotDcpt`.

This is the naturality square of `Submodule.mapQ`:

`mapQ (S' k) (S'.sub k) (d') ∘ mapQ (S k) (S'.sub k) (f) = mapQ … (f) ∘ mapQ … (d)`

both sides being `mapQ` of `d' ∘ f = f ∘ d` (the chain-map condition for `f`).

## Note on the `ℤ`-module diamond

The carrier-level definitions `SubData.quot`, `SubData.quotOf` and the component
helpers `SubData.quotCptMap`, `SubData.quotDcpt` are ordinary `def`s, so
`S.quot.X k` does not unfold at reducible transparency; this is the source of the
`↥(C.X k ⧸ S.sub k)` vs `S.quot.X k` mismatch (see `SubComplex.lean` and
`NOTES.md`).  We declare them `[local reducible]` for the scope of this file (with
`allowUnsafeReducibility`), and fix the intended `ℤ`-module structures with
`SubData.instModuleQuot`, so that instance synthesis produces the very structures
appearing in the definitions.
-/

namespace Work.Subdivision

open CategoryTheory

section

set_option allowUnsafeReducibility true
attribute [local reducible] SubData.quot SubData.quotOf SubData.quotCptMap SubData.quotDcpt

/-- `SubData.quotD k` is the `Submodule.mapQ` of the underlying differential, by
definition. -/
theorem quotD_eq_mapQ {C : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) (k : ℕ) :
    S.quotD k = Submodule.mapQ (S.sub (k + 1)) (S.sub k) (C.d (k + 1) k).hom
      (fun x hx => S.d_mem k x hx) := rfl

set_option linter.style.haveILetI false in
theorem quotCptMap_comm {C C' : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) (S' : SubData C')
    (f : C ⟶ C') (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (S.quotCptMap S' f hf (k + 1)) (S'.quotDcpt k) =
      CategoryTheory.CategoryStruct.comp (S.quotDcpt k) (S.quotCptMap S' f hf k) := by
  -- Fix the `ℤ`-module structures on the four quotients involved.
  letI a1 : Module ℤ (C.X (k + 1) ⧸ S.sub (k + 1)) := Submodule.Quotient.module (S.sub (k + 1))
  letI a0 : Module ℤ (C.X k ⧸ S.sub k) := Submodule.Quotient.module (S.sub k)
  letI b1 : Module ℤ (C'.X (k + 1) ⧸ S'.sub (k + 1)) := Submodule.Quotient.module (S'.sub (k + 1))
  letI b0 : Module ℤ (C'.X k ⧸ S'.sub k) := Submodule.Quotient.module (S'.sub k)
  -- Both sides are `ModuleCat.ofHom` of the underlying linear maps; combine the
  -- composite into a single `ofHom`.
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom]
  -- Replace `quotD` by its `mapQ` unfolding.
  rw [quotD_eq_mapQ S' k, quotD_eq_mapQ S k]
  -- `mapQ` is compatible with composition (`Submodule.mapQ_comp`), turning each
  -- side into a single `mapQ` of a composite map.
  rw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
  -- The two composite maps agree by the chain-map condition for `f`.
  have hcomp : (C'.d (k + 1) k).hom.comp (f.f (k + 1)).hom =
      (f.f k).hom.comp (C.d (k + 1) k).hom := by
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm f (k + 1) k)
    simpa only [ModuleCat.hom_comp] using h
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (p := S.sub (k + 1)) x ?_
  intro y
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (congrArg (fun φ => φ y) hcomp)

end

end Work.Subdivision
