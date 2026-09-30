import Mathlib
import Submission.Work.Subdivision.SubDataCpt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Subdivision

open CategoryTheory

/-- Naturality of the projection onto a quotient complex with respect to a chain
map carrying one subcomplex datum into another: the square

```
C.X k --f.f k--> C'.X k
  |                |
  proj            proj
  v                v
S.quot.X k --q--> S'.quot.X k
```

commutes.  Both composites send `x` to the class of `(f.f k).hom x`. -/
theorem proj_quotCptMap {C C' : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C)
    (S' : SubData C') (f : C ⟶ C') (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (f.f k) (S'.projcpt k) =
      CategoryTheory.CategoryStruct.comp (S.projcpt k) (S.quotCptMap S' f hf k) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  simp only [SubData.projcpt_apply, SubData.quotCptMap_apply]
  exact (Submodule.mapQ_mkQ (S.sub k) (S'.sub k) (f.f k).hom (h := hf k)).symm

end Work.Subdivision
