import Mathlib
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.DeltaHomology.chain_homology_isZero_of_dim_lt
import Submission.Work.Homology.Point
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.Corollaries
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.isIso_deltaChainMapSkelFun_zero
import Submission.Work.DeltaHomology.finite_skelSet_zero
import Submission.Work.DeltaHomology.isIso_homologyMap_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- **Base case `n = 0` of Hatcher 2.27 on the skeleton.**  For a realized `Δ`-complex, the
comparison chain map `deltaChainMapSkel χ 0 : (K.skel 0).chain ⟶ C_*(X⁰; ℤ)` is a
quasi-isomorphism.

Here `X⁰ = χ.skelSet 0` is the (finite) set of vertices of the realization, a finite discrete
Hausdorff subspace of `X`; `(K.skel 0).chain` is the free `ℤ`-module on the vertices concentrated
in degree `0`; and `C_*(X⁰; ℤ)` is the singular chain complex of a finite discrete space, which
has `H_0 ≅ ℤ^{K_0}` (with the classes of the vertices as a basis) and vanishing homology in
positive degrees.  Hence the comparison map, which in degree `0` is the identity `ℤ^{K_0} ≅
ℤ^{K_0}` (`deltaChainMapSkelFun_chainι`), is a quasi-isomorphism.

Useful inputs: `chain_homology_isZero_of_dim_lt` for the `Δ`-side vanishing in degrees `> 0`,
`DeltaCx.skel_card_eq` (`(K.skel 0).card j = K.card j` for `j ≤ 0` and `= 0` for `j > 0`),
and the computation of the singular homology of a finite discrete space
(`Work.Homology.Point`, `Work.Homology.SingHomologyClopen`, or `Work.Homology.Corollaries`).
The vertex-injectivity of `σ ↦ χ.cls 0 σ` uses `DeltaRealization.bij`, and discreteness of the
finite subspace `X⁰` uses `DeltaRealization.t2`. -/
theorem quasiOso_deltaChainMapSkel_zero {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) :
    QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel 0) := by
  classical
  haveI h2 : T2Space X := R.t2
  let chi : DeltaSimplexMap K X := R.toDeltaSimplexMap
  change QuasiIso (chi.deltaChainMapSkel 0)
  have hfin : Finite (↥(chi.skelSet 0)) := finite_skelSet_zero R
  haveI : Finite (↥(chi.skelSet 0)) := hfin
  haveI : TotallyDisconnectedSpace (↥(chi.skelSet 0)) := inferInstance
  let A : ModuleCat ℤ := ∐ (fun _ : ↥(chi.skelSet 0) => ZMod)
  let e : singChain ZMod (TopCat.of (chi.skelSet 0)) ≅ ChainComplex.alternatingConst.obj A :=
    AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℤ) ZMod _
  haveI : IsIso e.hom := inferInstance
  haveI hqe : QuasiIso e.hom := quasiIso_of_isIso e.hom
  rw [← quasiIso_iff_comp_right (chi.deltaChainMapSkel 0) e.hom]
  refine ⟨fun k => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hK : (K.skel 0).chain.d 1 0 = 0 := by
      have hz : IsZero ((K.skel 0).chainX 1) := chainX_isZero_of_dim_lt (K.skel 0) (by simp)
      exact hz.eq_of_src _ _
    have hL : (ChainComplex.alternatingConst.obj A).d 1 0 = 0 := rfl
    rw [isIso_homologyMap_zero_iff (chi.deltaChainMapSkel 0 ≫ e.hom) hK hL]
    haveI : IsIso ((chi.deltaChainMapSkel 0).f 0) := isIso_deltaChainMapSkelFun_zero R
    rw [HomologicalComplex.comp_f]
    infer_instance
  · exact IsZero.isIso (chain_homology_isZero_of_dim_lt (K.skel 0) (by simp; omega))
      (ChainComplex.alternatingConst_exactAt A k (by omega)).isZero_homology _

end Work.DeltaHomology
