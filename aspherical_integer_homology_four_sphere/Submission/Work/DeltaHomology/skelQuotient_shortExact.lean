import Mathlib
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The short exact sequence of the chain complexes of consecutive skeleta

For a finite `Δ`-complex `K` (`Work.DeltaHomology.DeltaCx`) and `k : ℕ`, the inclusion of the
`k`-skeleton in the `(k+1)`-skeleton induces a chain map

`(K.skel k).chain ⟶ (K.skel (k+1)).chain`

which is a monomorphism, so that

`0 ⟶ (K.skel k).chain ⟶ (K.skel (k+1)).chain ⟶ cokernel ⟶ 0`

is a short exact sequence of chain complexes of `ℤ`-modules.  This is the algebraic input to the
skeletal induction computing the homology of a `Δ`-complex.

The monomorphism is proved degreewise (`HomologicalComplex.mono_of_mono_f`):

* in degree `j ≤ k`, `K.skel k` and `K.skel (k+1)` have the same `j`-simplices, the map is the
  identity on index sets (up to the canonical identification of the cardinals) and hence has an
  explicit retraction, so it is a split monomorphism;
* in degree `j > k` the source `(K.skel k).chainX j` is a coproduct indexed by the empty type
  `Fin ((K.skel k).card j)`, hence a zero object, and every map out of a zero object is a
  monomorphism.
-/

namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise component of the inclusion of skeleta `K.skel k ⟶ K.skel (k+1)` on chains is
a monomorphism.

In degree `j ≤ k` the two skeleta have the same `j`-simplices (`DeltaCx.skel_card_eq`), the map on
coproducts is induced by the identity of the index sets, and the inverse bijection
`Fin.cast` provides an explicit retraction, exhibiting the map as a split monomorphism.  In degree
`j > k` the source `(K.skel k).chainX j` is a coproduct over the empty index type
(`DeltaCx.skel_card_eq_zero`), hence a zero object (`isZero_chainX_of_dim_lt`), and any map out of
a zero object is a monomorphism (`IsZero.mono`). -/
theorem mono_chainMapFun_skelLE (K : DeltaCx) (k j : ℕ) :
    Mono (DeltaCx.Hom.chainMapFun (K.skelLE (Nat.le_succ k)) j) := by
  by_cases hj : j ≤ k
  · -- `j ≤ k`: the two skeleta agree in degree `j` and the map is a split monomorphism.
    have hcard : (K.skel k).card j = (K.skel (k + 1)).card j := by
      rw [DeltaCx.skel_card_eq K k hj, DeltaCx.skel_card_eq K (k + 1) (by omega)]
    -- the retraction, induced by the inverse bijection of the index sets
    let ψ : (K.skel (k + 1)).chainX j ⟶ (K.skel k).chainX j :=
      Sigma.desc fun τ : Fin ((K.skel (k + 1)).card j) =>
        (K.skel k).chainι j (Fin.cast hcard.symm τ)
    have hcomp : DeltaCx.Hom.chainMapFun (K.skelLE (Nat.le_succ k)) j ≫ ψ = 𝟙 _ := by
      -- it suffices to check on the basis elements `(K.skel k).chainι j σ`
      apply DeltaCx.chainX_hom_ext
      intro σ
      rw [← Category.assoc, DeltaCx.Hom.chainMapFun_chainι, DeltaCx.skelLE_map,
        skelHomOfLe_eq K (Nat.le_succ k) hj σ]
      dsimp only [ψ]
      rw [Sigma.ι_comp_desc, Category.comp_id]
      -- `Fin.cast hcard.symm (Fin.cast _ σ) = σ`, since both sides have the same value
      refine congrArg (fun x : Fin ((K.skel k).card j) => (K.skel k).chainι j x) ?_
      apply Fin.ext
      simp only [Fin.val_cast]
    have hsplit : IsSplitMono (DeltaCx.Hom.chainMapFun (K.skelLE (Nat.le_succ k)) j) :=
      IsSplitMono.mk ⟨SplitMono.mk ψ hcomp⟩
    exact @IsSplitMono.mono _ _ _ _ _ hsplit
  · -- `j > k`: the source is a coproduct over the empty type, i.e. a zero object.
    have hz : IsZero ((K.skel k).chainX j) :=
      isZero_chainX_of_dim_lt (K.skel k) (by rw [DeltaCx.skel_dim]; omega)
    exact hz.mono _

/-- **The sequence of `Δ`-chain complexes of the skeleta is short exact.**  For a `Δ`-complex
`K` and `k : ℕ`, the inclusion of the `k`-skeleton induces a chain map
`(K.skel k).chain ⟶ (K.skel (k+1)).chain` which is a monomorphism, and the resulting sequence
`0 → (K.skel k).chain → (K.skel (k+1)).chain → cokernel → 0` is short exact.

Route: `ShortComplex.ShortExact.mk'` with `ShortComplex.exact_cokernel`, and `Mono` from
degreewise injectivity (`skel_card_eq`, `skel_card_eq_zero`: in degree `j ≤ k` the map is the
identity of the free module, and in degree `j > k` its source is `0`). -/
theorem skelQuotient_shortExact (K : DeltaCx) (k : ℕ) :
    (ShortComplex.mk (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
      (cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))))
      (cokernel.condition (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))))).ShortExact := by
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))) ?_ inferInstance
  -- `Mono` of the chain map, from the degreewise monomorphisms
  apply HomologicalComplex.mono_of_mono_f
  intro j
  exact mono_chainMapFun_skelLE K k j

end Work.DeltaHomology
