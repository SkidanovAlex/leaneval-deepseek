import Mathlib
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.ThomBordism.RelDuality.interiorHomology
import Submission.Work.ThomBordism.RelDuality.relClass_lift
import Submission.Work.ThomBordism.RelDuality.goodOfOpen
import Submission.Work.ThomBordism.RelDuality.doubleFundClass
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.Port.Glue
import Submission.Work.ThomBordism.Port.PdGoodUnivChart
import Submission.Work.ThomBordism.RelDuality.Supp2
import Submission.Work.ThomBordism.RelDuality.Supp3
import Submission.Work.ThomBordism.RelDuality.Comp
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.Crux.relCapPair_natural
import Submission.Work.Cohomology.capRelAux
import Submission.Work.ThomBordism.doubleFC.interiorData
import Submission.Work.ThomBordism.localGenAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.RelDuality

theorem lefschetzDualityBdry_of_pieces
    (P1 : ∀ {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M],
      ∀ m : ℕ, Function.Bijective (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ
          (TopCat.of {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M})
          (TopCat.of M)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) m))
    (P2 : ∀ {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M] (k : ℕ),
      ∀ u : (Work.Cohomology.relComplex ℤ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology k,
        ∃ (K : Set M) (hK : K ⊆ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}),
          IsCompact K ∧
          ∃ x : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k,
            (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) x
              = u)
    (P3 : ∀ {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
      [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
      (c : (Work.Cohomology.singularChains ℤ M).homology N)
      (hc : ∀ x : M, Submodule.span ℤ {(HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N c)} = ⊤)
      (hN : 1 ≤ N), ∀ (U : Set M) (hU : IsOpen U), Work.Cohomology.Good N c U hU)
    (P4 : ∀ {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Work.ThomBordism.Double 8 M)]
      [T2Space (Work.ThomBordism.Double 8 M)] [CompactSpace (Work.ThomBordism.Double 8 M)]
      (w : (Work.Cohomology.relChains (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology 9)
      (hw : ∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M),
        Submodule.span ℤ {(HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace 9).boundary M) x hx) 9 w)} = ⊤),
      ∃ c : (Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.ThomBordism.Double 8 M))).homology 9,
        (∀ x : Work.ThomBordism.Double 8 M, Submodule.span ℤ {(HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsProj (TopCat.of (Work.ThomBordism.Double 8 M)) {y | y ≠ x}) 9 c)}
            = ⊤) ∧
        (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          HomologicalComplex.homologyMap (Work.ThomBordism.projSecondHalf (M := M)) 9 c
            = ε • HomologicalComplex.homologyMap (Work.ThomBordism.inclRelMap (M := M)) 9 w)) :
    ∀ {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F),
      Work.ThomBordism.LefschetzDualityBdry W := by
  intro ι _ F W
  letI : ChartedSpace (EuclideanHalfSpace (8 + 1)) W.W := W.chartedSpace
  letI : IsManifold (modelWithCornersEuclideanHalfSpace (8 + 1)) 1 W.W := W.isManifold
  haveI : T2Space (Work.ThomBordism.Double 8 W.W) :=
    Work.ThomBordism.DblT2.t2Space_double (n := 8) (M := W.W)
  haveI : CompactSpace (Work.ThomBordism.Double 8 W.W) :=
    Work.ThomBordism.doubleCompact (n := 8) (M := W.W)
  have hP3 : ∀ {N : ℕ}
      [ChartedSpace (EuclideanSpace ℝ (Fin N)) (Work.ThomBordism.Double 8 W.W)]
      (c : (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.ThomBordism.Double 8 W.W))).homology N)
      (hc : ∀ x : Work.ThomBordism.Double 8 W.W, Submodule.span ℤ {(HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Work.ThomBordism.Double 8 W.W)) {y | y ≠ x})) N c)} = ⊤)
      (hN : 1 ≤ N), ∀ (U : Set (Work.ThomBordism.Double 8 W.W)) (hU : IsOpen U),
        Work.Cohomology.Good N c U hU := by
    intro N inst c hc hN U hU
    exact P3 (M := TopCat.of (Work.ThomBordism.Double 8 W.W)) c hc hN U hU
  obtain ⟨cD, _, hMcls, hgood⟩ :=
    Work.ThomBordism.RelDuality.doubleClassPieces (M := W.W) W.w W.w_fund hP3
  have hcomp : Work.ThomBordism.RelDuality.CompHyp (M := W.W) W.w cD :=
    Work.ThomBordism.RelDuality.localFundClass_image_eq (M := W.W) W.w cD hMcls
  exact Work.ThomBordism.RelDuality.lefschetzDuality_of_comp (M := W.W) W.w cD hgood hcomp
    (fun m => P1 (M := W.W) m) (fun k => P2 (M := W.W) k)

end Work.ThomBordism.RelDuality
