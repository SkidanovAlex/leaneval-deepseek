import Mathlib
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.Homology.Basic
import Submission.Work.DeltaHomology.SkeletonMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inclusion of consecutive skeleta of a realization

For a `Δ`-complex `K` with characteristic maps `χ` in `X` and `k : ℕ`, the `k`-skeleton
`χ.skelSet k` is contained in the `(k+1)`-skeleton `χ.skelSet (k+1)`.  This file packages the
resulting inclusion of subspaces as a morphism of `TopCat`,
`χ.skelIncl k : TopCat.of (χ.skelSet k) ⟶ TopCat.of (χ.skelSet (k + 1))`,
together with its defining equation and its compatibility with the inclusions into `X`.

It is the input to the compatibility `deltaChainMapSkel k ≫ singChainMap (skelIncl k) =
chainMap (K.skelLE _) ≫ deltaChainMapSkel (k+1)` of the comparison maps on consecutive skeleta
(`Work.DeltaHomology.DeltaSimplexMap.deltaChainMapSkel_natural`), which is the chain-level input
of the skeleta induction of Hatcher's theorem.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- The inclusion of the `k`-skeleton of a realization in the `(k+1)`-skeleton, as a map of
the two subspaces of `X`. -/
def DeltaSimplexMap.skelIncl (χ : DeltaSimplexMap K X) (k : ℕ) :
    TopCat.of (χ.skelSet k) ⟶ TopCat.of (χ.skelSet (k + 1)) :=
  TopCat.ofHom ⟨fun x => ⟨(x : X), χ.skelSet_mono (Nat.le_succ k) x.2⟩,
    Continuous.subtype_mk continuous_subtype_val
      (fun x => χ.skelSet_mono (Nat.le_succ k) x.2)⟩

@[simp]
theorem DeltaSimplexMap.skelIncl_coe (χ : DeltaSimplexMap K X) (k : ℕ)
    (x : ↥(χ.skelSet k)) :
    ((χ.skelIncl k x : ↥(χ.skelSet (k + 1))) : X) = (x : X) := rfl

/-- The inclusion of consecutive skeleta, followed by the inclusion of the `(k+1)`-skeleton in
`X`, is the inclusion of the `k`-skeleton in `X`. -/
theorem DeltaSimplexMap.skelIncl_comp_incl (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.skelIncl k ≫ incl (χ.skelSet (k + 1)) = incl (χ.skelSet k) := by
  apply TopCat.hom_ext
  ext x
  rfl

end

end Work.DeltaHomology
