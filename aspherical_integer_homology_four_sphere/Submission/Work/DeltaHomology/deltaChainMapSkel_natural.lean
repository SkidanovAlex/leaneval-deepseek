import Mathlib
import Submission.Work.DeltaHomology.SkelInclDefs
import Submission.Work.Homology.Pairs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- The inclusion `K.skel n → K` of `Δ`-complexes is compatible with the inclusions of skeleta:
for `n ≤ m`, sending a simplex of the `n`-skeleton into `K` through the `m`-th skeleton agrees
with sending it through the `n`-th skeleton. -/
theorem skelMap_skelHomOfLe (K : DeltaCx) {n m : ℕ} (h : n ≤ m) {j : ℕ}
    (σ : Fin (skelCard K n j)) :
    skelMap K m (skelHomOfLe K h σ) = skelMap K n σ := by
  by_cases hj : j ≤ n
  · rw [skelMap_eq K n hj, skelHomOfLe_eq K h hj, skelMap_eq K m (by omega)]
    apply Fin.ext
    simp only [Fin.val_cast]
  · exact Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ)

/-- The inclusion of the `k`-skeleton into `K` factors through the inclusion of the
`(k+1)`-skeleton: `(K.skel k ⟶ K.skel (k+1)) ≫ (K.skel (k+1) ⟶ K) = (K.skel k ⟶ K)`. -/
theorem skelHom_comp_skelLE (K : DeltaCx) (k : ℕ) :
    (K.skelLE (Nat.le_succ k)).comp (K.skelHom (k + 1)) = K.skelHom k := by
  apply DeltaCx.Hom.ext
  intro j σ
  simp only [DeltaCx.Hom.comp_map, DeltaCx.skelHom_map, DeltaCx.skelLE_map]
  exact skelMap_skelHomOfLe K (Nat.le_succ k) σ

/-- **Compatibility of the comparison chain map with the inclusions of consecutive skeleta.**
For a `Δ`-complex `K` with characteristic maps `χ` in `X`, the two ways of going from the
`Δ`-chains of the `k`-skeleton to the singular chains of the `(k+1)`-skeleton agree:
`δ_k ≫ singChainMap (skelIncl k) = chainMap (K.skelLE (Nat.le_succ k)) ≫ δ_{k+1}`,
where `δ_k = χ.deltaChainMapSkel k` and `χ.skelIncl k : TopCat.of (χ.skelSet k) ⟶
TopCat.of (χ.skelSet (k+1))` is the inclusion of subspaces (defined in
`Submission.Work.DeltaHomology.SkelInclDefs`).

Route: `inclChain ZMod X (χ.skelSet (k+1))` is a monomorphism (`inclChain_mono`, in
`Work.Homology.Pairs`), so it suffices to check after composing with it on the right.  The
left-hand side becomes `δ_k ≫ inclChain ZMod X (χ.skelSet k)`, i.e.
`chainMap (K.skelHom k) ≫ χ.deltaChainMap` by `deltaChainMapSkel_compat χ k`; the right-hand side
becomes `chainMap ((K.skelLE (Nat.le_succ k)).comp (K.skelHom (k+1))) ≫ χ.deltaChainMap` by
`deltaChainMapSkel_compat χ (k+1)` and `chainMap_comp`, so it suffices to know
`(K.skelLE (Nat.le_succ k)).comp (K.skelHom (k+1)) = K.skelHom k`, which follows from
`DeltaCx.Hom.ext`, `skelMap_eq` and `skelHomOfLe_eq`.  One also needs
`DeltaSimplexMap.skelIncl_comp_incl` (in `SkelInclDefs`) and `singChainMap_comp`. -/
theorem deltaChainMapSkel_natural {K : DeltaCx} {X : TopCat}
    (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.deltaChainMapSkel k ≫ singChainMap ZMod (χ.skelIncl k)
      = DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)) ≫ χ.deltaChainMapSkel (k + 1) := by
  haveI : Mono (inclChain ZMod X (χ.skelSet (k + 1))) := inclChain_mono ZMod X _
  have hA : (χ.deltaChainMapSkel k ≫ singChainMap ZMod (χ.skelIncl k))
        ≫ inclChain ZMod X (χ.skelSet (k + 1))
      = DeltaCx.Hom.chainMap (K.skelHom k) ≫ χ.deltaChainMap := by
    rw [Category.assoc,
      ← singChainMap_comp ZMod (χ.skelIncl k) (incl (χ.skelSet (k + 1))),
      DeltaSimplexMap.skelIncl_comp_incl]
    exact DeltaSimplexMap.deltaChainMapSkel_compat χ k
  have hB : (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
          ≫ χ.deltaChainMapSkel (k + 1))
        ≫ inclChain ZMod X (χ.skelSet (k + 1))
      = DeltaCx.Hom.chainMap (K.skelHom k) ≫ χ.deltaChainMap := by
    rw [Category.assoc,
      DeltaSimplexMap.deltaChainMapSkel_compat χ (k + 1),
      ← Category.assoc,
      ← DeltaCx.Hom.chainMap_comp,
      skelHom_comp_skelLE]
  refine (cancel_mono (inclChain ZMod X (χ.skelSet (k + 1)))).mp ?_
  rw [hA, hB]

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The file as delivered carries two identical `namespace Work.DeltaHomology` lines, so the
declaration above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology`.
The statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`,
which is the name under which the rest of the project refers to it
(`Work.DeltaHomology.deltaChainMapSkel_natural`). -/

/-- **Compatibility of the comparison chain map with the inclusions of consecutive skeleta**
(flat name). -/
theorem deltaChainMapSkel_natural {K : DeltaCx} {X : TopCat}
    (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.deltaChainMapSkel k ≫ singChainMap ZMod (χ.skelIncl k)
      = DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)) ≫ χ.deltaChainMapSkel (k + 1) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.deltaChainMapSkel_natural χ k

end Work.DeltaHomology
