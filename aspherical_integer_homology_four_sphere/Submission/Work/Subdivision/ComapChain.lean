/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataSES

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative subcomplexes of a filtration

Let `S` be a subcomplex of `C` and `T k ≤ S.sub k` degreewise submodules closed
under the differential of `C`.  Then the corresponding subcomplex of `S.chain`
is `SubData.comapChain S T hT hTd`, whose `k`-chains are the elements of `S` in
degree `k` whose underlying element of `C` lies in `T k`.

This is the general mechanism producing the relative subcomplexes
`A n ⊆ A (n+1)` of the skeletal filtrations of a `PolyCW`: there
`S = cellSub (n+1)` and `T k = cellSubMod n k`.

## Note on the ℤ-module diamond

The canonical `ℤ`-module structures `Submodule.module` and
`Submodule.Quotient.module` are given priority `1100` in `SubComplex.lean`; we
also mark `SubData.chain` and `SubData.comapChain` reducible, so that the
carrier `↥((S.comapChain T hT hTd).chain.X k)` is seen to be
`↥(Submodule.comap (Submodule.subtype (S.sub k)) (T k))`.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

set_option allowUnsafeReducibility true
attribute [reducible] SubData.chain

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

/-- The subcomplex of `S.chain` cut out by degreewise submodules `T k ≤ S.sub k`
which are closed under the differential of `C`.  This is the general mechanism
producing the relative subcomplexes `A n ⊆ A (n+1)` of the skeletal
filtrations. -/
def comapChain (S : SubData C) (T : ∀ k, Submodule ℤ (C.X k))
    (hT : ∀ k, T k ≤ S.sub k)
    (hTd : ∀ k (x : C.X (k + 1)), x ∈ T (k + 1) → (C.d (k + 1) k).hom x ∈ T k) :
    SubData S.chain where
  sub k := Submodule.comap (Submodule.subtype (S.sub k)) (T k)
  d_mem k x hx := by
    refine Submodule.mem_comap.mpr ?_
    rw [S.chain_d_eq k, S.dLcpt_apply k]
    exact hTd k (Submodule.subtype (S.sub (k + 1)) x) (Submodule.mem_comap.mp hx)

attribute [reducible] SubData.comapChain

end SubData

end

end Work.Subdivision
