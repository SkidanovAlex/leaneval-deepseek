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
# The restriction of a chain map to compatible subcomplexes commutes with the
differentials

For a chain map `f : C ⟶ C'` between chain complexes of `ℤ`-modules and
subcomplex data `S` of `C`, `S'` of `C'` with `f` carrying `S` into `S'`, the
degreewise restriction `S.restrictCptMap S' f hf k` is a morphism of chain
complexes `S.chain ⟶ S'.chain`: it commutes with the differentials.

The proof is the usual elementwise computation.  The only subtlety is the
`ℤ`-module diamond on the carriers of the submodules: the `Module ℤ` structure
stored in `S.chain.X k` is only equal to the one used in `SubData.dL k` up to
definitional unfolding, so the two sides are compared after a `change` that
reduces both to the corresponding raw differentials of `C` and `C'`, where the
chain-map condition `HomologicalComplex.Hom.comm` applies.
-/

namespace Work.Subdivision

open CategoryTheory

theorem restrictCptMap_comm {C C' : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) (S' : SubData C')
    (f : C ⟶ C') (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (S.restrictCptMap S' f hf (k + 1)) (S'.dLcpt k) =
      CategoryTheory.CategoryStruct.comp (S.dLcpt k) (S.restrictCptMap S' f hf k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, SubData.restrictCptMap_apply, SubData.dLcpt_apply]
  change (C'.d (k + 1) k).hom ((f.f (k + 1)).hom (Subtype.val x)) =
    (f.f k).hom ((C.d (k + 1) k).hom (Subtype.val x))
  exact congrArg (fun g : C.X (k + 1) →ₗ[ℤ] C'.X k => g (Subtype.val x))
    (congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm f (k + 1) k))

end Work.Subdivision
