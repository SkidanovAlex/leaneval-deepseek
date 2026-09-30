import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

set_option autoImplicit false

/-!
# The comparison map on the skeleta is a chain map

For a `Δ`-complex `K` with characteristic maps `χ` in a space `X`, the `k`-skeleton
`X^k = χ.skelSet k` is a subspace of `X`, and the comparison map
`χ.deltaChainMapSkelFun k : (K.skel k).chain ⟶ C_*(X^k; ℤ)` (sending a simplex `σ`
of the skeleton to the singular simplex induced by the corestricted characteristic
map) is a chain map.  This file proves the commutation with the differentials,
together with the two elementary lemmas on which it rests:

* `toSSet_delta_symm` : the face of a singular simplex (a continuous map into `Y`,
  transported to the singular simplicial set) is the transport of the composition
  with `StdSimplex.map i.succAbove`;
* `DeltaSimplexMap.clsInSkelSet_comp_succAbove` : the corestricted characteristic
  maps commute with faces (a transport of `DeltaSimplexMap.face_compat` through
  `DeltaSimplexMap.clsInSkelSet_coe`, using `skelMap_face_face`);
* `DeltaSimplexMap.singFace_chiInSkelSet` : the resulting statement at the level of
  the corestricted singular simplices.

The main result `deltaChainMapSkelFun_comm` is then read off on basis simplices.
-/

variable {K : DeltaCx} {X : TopCat}

/-- The face `δ_i` of a singular simplex of `Y`, formulated with `TopCat.toSSetObjEquiv`:
the `i`-th face corresponds to precomposition with `StdSimplex.map i.succAbove`. -/
theorem toSSet_delta_symm {Y : TopCat} {n : ℕ} (i : Fin (n + 2))
    (g : C(StdSimplex ℝ (Fin (n + 2)), Y)) :
    (TopCat.toSSet.obj Y).δ i
        ((TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk (n + 1)))).symm g)
      = (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n))).symm
          (g.comp ⟨StdSimplex.map i.succAbove, by fun_prop⟩) := by
  apply (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n))).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The corestricted characteristic maps of a `Δ`-complex commute with faces:
`χ (d_i σ)` is the `i`-th face of `χ σ`, as continuous maps into the `k`-skeleton. -/
theorem DeltaSimplexMap.clsInSkelSet_comp_succAbove (χ : DeltaSimplexMap K X)
    {k j : ℕ} (h : j + 1 ≤ k) (σ : Fin (skelCard K k (j + 1))) (i : Fin (j + 2)) :
    (χ.clsInSkelSet k h (skelMap K k σ)).comp ⟨StdSimplex.map i.succAbove, by fun_prop⟩
      = χ.clsInSkelSet k (by omega : j ≤ k) (skelMap K k (skelFace K k σ i)) := by
  ext z
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, DeltaSimplexMap.clsInSkelSet_coe,
    DeltaSimplexMap.cls]
  rw [← TopCat.toSSetObjEquiv_δ_apply (X := X) (n := j) (χ.χ (j + 1) (skelMap K k σ)) i z]
  change ((X.toSSetObjEquiv (Opposite.op ⦋j⦌)) (singFace i (χ.χ (j + 1) (skelMap K k σ)))) z
      = ((X.toSSetObjEquiv (Opposite.op ⦋j⦌)) (χ.χ j (skelMap K k (skelFace K k σ i)))) z
  rw [← χ.face_compat (skelMap K k σ) i, ← skelMap_face_face K k σ i]

/-- The face of the corestricted singular simplex of a skeleton simplex is again the
corestricted singular simplex of the corresponding face. -/
theorem DeltaSimplexMap.singFace_chiInSkelSet (χ : DeltaSimplexMap K X)
    {k j : ℕ} (h : j + 1 ≤ k) (σ : Fin (skelCard K k (j + 1))) (i : Fin (j + 2)) :
    (TopCat.toSSet.obj (TopCat.of (χ.skelSet k))).δ i (χ.chiInSkelSet k h (skelMap K k σ))
      = χ.chiInSkelSet k (by omega : j ≤ k) (skelMap K k (skelFace K k σ i)) := by
  rw [DeltaSimplexMap.chiInSkelSet, DeltaSimplexMap.chiInSkelSet, toSSet_delta_symm]
  exact congrArg _ (DeltaSimplexMap.clsInSkelSet_comp_succAbove χ h σ i)

/-- The degreewise comparison map on the `k`-skeleton is a chain map (in the
orientation required by `ChainComplex.ofHom`):
`χ.deltaChainMapSkelFun k (j+1) ≫ d = (K.skel k).chainD j ≫ χ.deltaChainMapSkelFun k j`.

Route: check on the basis simplices `(K.skel k).chainι j σ` (via
`DeltaCx.chainX_hom_ext`, `DeltaSimplexMap.deltaChainMapSkelFun_chainι`,
`DeltaCx.ι_chainD` and `SSet.ιChainComplex_d`); the two sums agree term by term
because the corestricted characteristic maps commute with faces (a transport of
`DeltaSimplexMap.face_compat` through `DeltaSimplexMap.clsInSkelSet`, which is
`rfl`-level on values via `DeltaSimplexMap.clsInSkelSet_coe`, together with
`skelMap_face_face` from `Submission.Work.DeltaHomology.skelMap_face_face`).  In the
case `k ≤ j` both sides are maps out of the zero object `(K.skel k).chainX (j+1) = 0`. -/
theorem deltaChainMapSkelFun_comm {K : DeltaCx} {X : TopCat} (χ : DeltaSimplexMap K X)
    (k j : ℕ) :
    χ.deltaChainMapSkelFun k (j + 1)
        ≫ (singChain ZMod (TopCat.of (χ.skelSet k))).d (j + 1) j
      = (K.skel k).chainD j ≫ χ.deltaChainMapSkelFun k j := by
  by_cases hk : j + 1 ≤ k
  · -- Case `j + 1 ≤ k`: check on basis simplices.
    have hj : j ≤ k := by omega
    apply DeltaCx.chainX_hom_ext
    intro σ
    rw [← Category.assoc, DeltaSimplexMap.deltaChainMapSkelFun_chainι χ hk]
    erw [SSet.ιChainComplex_d]
    rw [← Category.assoc, DeltaCx.ι_chainD, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, DeltaSimplexMap.deltaChainMapSkelFun_chainι χ hj]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    congr 1
    exact DeltaSimplexMap.singFace_chiInSkelSet χ hk σ i
  · -- Case `k ≤ j`: both sides are maps out of the zero object `(K.skel k).chainX (j+1)`.
    have hz : IsZero ((K.skel k).chainX (j + 1)) :=
      isZero_chainX_of_dim_lt (K.skel k) (by rw [DeltaCx.skel_dim]; omega)
    exact hz.eq_of_src _ _

end Work.DeltaHomology
