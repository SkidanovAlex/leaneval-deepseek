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
# The inclusion factors through the restriction of a chain map

For a chain map `f : C ⟶ C'` of chain complexes of `ℤ`-modules and subcomplex
data `S` of `C`, `S'` of `C'` with `f` carrying `S` into `S'`, the inclusion
`S.inclcpt k : S.chain.X k ⟶ C.X k` followed by `f.f k` agrees with the
restriction `S.restrictCptMap S' f hf k : S.chain.X k ⟶ S'.chain.X k` followed
by the inclusion `S'.inclcpt k`:

`S.inclcpt k ≫ f.f k = S.restrictCptMap S' f hf k ≫ S'.inclcpt k`.

The proof is the obvious elementwise computation: both sides send `x` to
`(f.f k).hom x`, and the two are equal up to unfolding the coercions of the
submodules.
-/

namespace Work.Subdivision

open CategoryTheory

theorem incl_restrictCptMap {C C' : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C)
    (S' : SubData C') (f : C ⟶ C') (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (S.inclcpt k) (f.f k) =
      CategoryTheory.CategoryStruct.comp (S.restrictCptMap S' f hf k) (S'.inclcpt k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, SubData.inclcpt_apply, SubData.restrictCptMap_apply]
  rfl

end Work.Subdivision
