import Mathlib
import Submission.Work.Subdivision.PieceQuot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `sdPieceMapLin` is a chain map

The degreewise identification `PolyCW.sdPieceMapLin P n E ha k` (`PieceQuot.lean`)
sends the local complex `locCx P a` of a new `(n+1)`-cell `a` into the quotient
`(sdPiece P n E a).quot` of the subdivided level.  This file proves that it
commutes with the differentials, i.e. that it is a chain map: for every `k`,

`sdPieceMapLin_{k+1} ≫ (sdPiece).quot.d = (locCx a).d ≫ sdPieceMapLin_k`.

Both composites send the class of `y ∈ leSub a (k+1)` to the class of the chain
`D k y`; the only point to check is that the two representatives — one obtained by
the (restricted) differential of the refined subdivided filtration
`sdTop P n (insert a E)` and one by the differential of `leSub a` — agree in the
ambient chain module `chainMod P.Cell k`, where they are literally both `D k y`.

## Note on the ℤ-module/transparency diamond

As in `SubDataCpt.lean` and `quotCptMap_comm.lean`, the carrier-level definitions
`SubData.quot`, `SubData.quotOf` (and here also the filtrations `sdTop`, `sdPiece`,
`sdChain` and the local submodules `leSub`, `ltSub`) are ordinary `def`s/abbrevs,
so `(S.quot).X k` does not unfold at reducible transparency: this is the source of
the `↑(C.X k ⧸ S.sub k)` versus `S.quot.X k` mismatch.  We declare them `[local
reducible]` for the scope of this file (with `allowUnsafeReducibility`), which lets
`rw` see through `SubData.quot_d` and `ModuleCat.hom_comp`.
-/

namespace Work.Subdivision

open CategoryTheory

section

set_option allowUnsafeReducibility true
attribute [local reducible] SubData.quot SubData.quotOf PolyCW.sdTop PolyCW.sdPiece
  PolyCW.sdTopMod PolyCW.leSub PolyCW.ltSub PolyCW.locRel PolyCW.locMod PolyCW.sdChain

theorem sdPieceMapLin_comm (P : Work.Subdivision.PolyCW) (n : ℕ)
    (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (ModuleCat.ofHom (Work.Subdivision.PolyCW.sdPieceMapLin P n E ha (k + 1)))
        (((Work.Subdivision.PolyCW.sdPiece P n E a).quot).d (k + 1) k) =
      CategoryTheory.CategoryStruct.comp
        ((Work.Subdivision.PolyCW.locCx P a).d (k + 1) k)
        (ModuleCat.ofHom (Work.Subdivision.PolyCW.sdPieceMapLin P n E ha k)) := by
  -- Rewrite both differentials as `ModuleCat.ofHom` of the underlying linear maps.
  apply ModuleCat.hom_ext
  rw [SubData.quot_d, PolyCW.locCx_d]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  simp only [ModuleCat.hom_ofHom]
  -- Compare the two linear maps
  -- `(sdPiece).quotD k ∘ sdPieceMapLin (k+1)` and `sdPieceMapLin k ∘ locD a k`
  -- on the class of `y ∈ leSub a (k+1)`.
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (p := P.locRel a (k + 1)) x ?_
  intro y
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  -- Evaluate both maps on `[y]`.
  rw [P.sdPieceMapLin_apply n E ha (k + 1) y]
  rw [P.locD_mk]
  rw [P.sdPieceMapLin_apply n E ha k (P.leSubD a k y)]
  rw [SubData.quotD_apply]
  -- It remains to identify the two representatives in degree `k`.
  refine congrArg Submodule.Quotient.mk ?_
  apply Subtype.ext
  -- Both are the restricted ambient differential `D k` applied to `y`.
  rw [SubData.chain_d (S := P.sdTop n (insert a E)) k, ModuleCat.hom_ofHom]
  rw [SubData.dL_apply (S := P.sdTop n (insert a E)) k]
  rw [PolyCW.sdChain_d]
  rw [ModuleCat.hom_ofHom]
  simp only [PolyCW.sdInc, Submodule.coe_inclusion]
  exact (P.leSubD_apply a k y).symm

end

end Work.Subdivision
