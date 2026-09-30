import Mathlib
import Submission.Work.Subdivision.SubdivChain
import Submission.Work.Subdivision.D_subdivCell
import Submission.Work.Subdivision.subdivCell_support
import Submission.Work.Subdivision.D_coneLM
import Submission.Work.Subdivision.D_coneLM_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision chain map commutes with the differential

`PolyCW.subdivCpt P hdd k` is the `k`-th component of the subdivision chain map
`cellChain P ⟶ sdChain P`: it is the linear map `subdivLM P k` promoted to a
morphism of `ModuleCat ℤ` (subdivision of the cellular chain complex is the
barycentric subdivision, so `subdivLM k : cellMod P k →ₗ chainMod P.Cell k`).

The compatibility of these components with the differentials is exactly the
linear identity proved in `D_subdivCell.lean`, namely `PolyCW.subdivLM_chain`:

`D k (subdivLM (k+1) z) = subdivLM k (cellD k z)`

for every `z`.  Since in a category `CategoryStruct.comp f g` denotes the
composite `f ≫ g` (i.e. `g ∘ f`), the statement below is precisely the underlying
map identity of the two composites of linear maps:

* the left composite is `D k ∘ subdivLM (k+1)`, and
* the right composite is `subdivLM k ∘ cellD k`,

which agree by `PolyCW.subdivLM_chain`.
-/

namespace Work.Subdivision

theorem subdivCpt_comm (P : PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (P.subdivCpt hdd (k + 1)) ((P.sdChain).d (k + 1) k) =
      CategoryTheory.CategoryStruct.comp ((P.cellChain hdd).d (k + 1) k) (P.subdivCpt hdd k) := by
  apply ModuleCat.hom_ext
  ext z
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [PolyCW.subdivCpt_apply, PolyCW.sdChain_d, PolyCW.cellChain_d]
  exact P.subdivLM_chain hdd haug k z

end Work.Subdivision
