import Mathlib
import Submission.Work.BridgeSquare.Data
import Submission.Work.BridgeSquare.chiRep_mem_Tset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

open Work.HomologyIso.Gen (mbarDim)

/-! ## §1  The cusp parametrisation is a homeomorphism onto the truncation set -/

/-- The inverse of the cusp parametrisation, as a map on the truncation set. -/
def cuspInvT (p : Work.FoldInst.Tset) : Cop :=
  Work.Space.Split.homeoBdrySubSig Work.RTOwed.rtData.core
    (@Work.Space.Assembly.glue Work.RTOwed.rtData.core p)

theorem cuspMap_cuspInvT (p : Work.FoldInst.Tset) :
    (cuspMap (cuspInvT p) : Work.FoldInst.Mbar) = (p : Work.FoldInst.Mbar) := by
  rw [cuspInvT, cuspMap]
  simp only [TopCat.ofHom, TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Homeomorph.symm_apply_apply, Work.Space.Assembly.tauBdry_apply]
  exact congrArg Subtype.val (Homeomorph.apply_symm_apply _ p)

theorem cuspMap_mem_Tset (x : Cop) :
    (cuspMap x : Work.FoldInst.Mbar) ∈ Work.FoldInst.Tset := by
  rw [cuspMap]
  simp only [TopCat.ofHom, TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Work.Space.Assembly.tauBdry_apply]
  exact (@Work.Space.Assembly.glue Work.RTOwed.rtData.core).symm _ |>.2

theorem cuspMap_injective :
    Function.Injective (fun x : Cop => (cuspMap x : Work.FoldInst.Mbar)) := by
  intro x y h
  simp only [cuspMap, TopCat.ofHom, TopCat.hom_ofHom, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Work.Space.Assembly.tauBdry_apply] at h
  have h1 := Subtype.coe_injective h
  have h2 := (Homeomorph.injective (@Work.Space.Assembly.glue Work.RTOwed.rtData.core).symm) h1
  exact (Homeomorph.injective (Work.Space.Split.homeoBdrySubSig Work.RTOwed.rtData.core).symm) h2

theorem range_cuspMap :
    Set.range (fun x : Cop => (cuspMap x : Work.FoldInst.Mbar)) = Work.FoldInst.Tset := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩; exact cuspMap_mem_Tset x
  · intro hp
    exact ⟨cuspInvT ⟨p, hp⟩, cuspMap_cuspInvT ⟨p, hp⟩⟩

theorem continuous_cuspInvT : Continuous (fun p : Work.FoldInst.Tset => cuspInvT p) := by
  change Continuous ((fun q => (Work.Space.Split.homeoBdrySubSig Work.RTOwed.rtData.core) q) ∘
    (fun p : Work.FoldInst.Tset => (@Work.Space.Assembly.glue Work.RTOwed.rtData.core) p))
  exact (Homeomorph.continuous (Work.Space.Split.homeoBdrySubSig Work.RTOwed.rtData.core)).comp
    (Homeomorph.continuous (@Work.Space.Assembly.glue Work.RTOwed.rtData.core))

/-- The inverse of the cusp parametrisation, as a continuous map. -/
def cuspInvCM : C(Work.FoldInst.Tset, Cop) :=
  ⟨cuspInvT, continuous_cuspInvT⟩

/-! ## §2  The singular chain of a continuous map -/

/-- The basis element of the singular chain group associated to a continuous map. -/
def singGen {X : TopCat} {n : ℕ} (u : C(StdSimplex ℝ (Fin (n+1)), X)) :
    (Work.Homology.singChain Work.Homology.ZMod X).X n :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod)
    ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm u)) (1 : ℤ)

theorem singGen_natural {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (u : C(StdSimplex ℝ (Fin (n+1)), X)) :
    (Work.Homology.singChainMap Work.Homology.ZMod f).f n (singGen u)
      = singGen (⟨fun w => f (u w), (TopCat.Hom.hom f).continuous.comp u.continuous⟩ :
          C(StdSimplex ℝ (Fin (n+1)), Y)) := by
  have key := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) Work.Homology.ZMod
    ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm u)
  have h2 : (CategoryTheory.ConcreteCategory.hom
        ((SSet.chainComplexMap (TopCat.toSSet.map f) Work.Homology.ZMod).f n))
        (CategoryTheory.ConcreteCategory.hom
          ((TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod)
            ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm u)) 1)
      = CategoryTheory.ConcreteCategory.hom
          ((TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod)
            ((ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))))
              ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm u))) 1 := by
    rw [← CategoryTheory.comp_apply, key]
  exact h2

/-! ## §3  The characteristic maps of the root simplices of a truncation cell -/

theorem chi_rootSimplex_mem_Tset (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e)
    (hc : ∃ c : Fin 48,
      c ∈ Work.MbarHomology.qTightC (Work.MbarHomology.Mbar.rootCx n e).idx ∧ 24 ≤ c.val) :
    ∀ w, Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s) w
      ∈ Work.FoldInst.Tset := by
  intro w
  have h1 : Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s)
      = ⟨fun w => Work.MbarHomology.Mbar.chiRep
          (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n, hn⟩ e), s) w,
        Work.MbarHomology.Mbar.continuous_chiRep _⟩ := by
    unfold Work.MbarHomology.Mbar.chi
    rw [show Work.MbarHomology.mbarEquiv n (Work.MbarHomology.Mbar.rootSimplex n hn e s)
        = Quotient.mk (Work.MbarHomology.flagSetoid n)
            (Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n, hn⟩ e), s) from
      Equiv.apply_symm_apply _ _]
    exact Work.MbarHomology.Mbar.chiQuot_mk n _
  have hidx : (Work.MbarHomology.Mbar.rootCx n e).idx
      = Work.MbarHomology.Mbar.moRoot (Work.MbarHomology.Mbar.moCid ⟨n, hn⟩ e) := by
    rw [Work.MbarHomology.Mbar.rootCx_of_lt hn]
  have hc' : ∃ c : Fin 48,
      c ∈ Work.MbarHomology.qTight (Work.MbarHomology.Mbar.topIdx
        ((Work.MbarHomology.Mbar.moRootC (Work.MbarHomology.Mbar.moCid ⟨n, hn⟩ e), s) :
          Work.MbarHomology.FlagQ n).2) ∧ 24 ≤ c.val := by
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, ?_, hc2⟩
    rw [Work.MbarHomology.Mbar.topIdx_rootNode n hn e s hs]
    rw [← Work.MbarHomology.qTightC_eq, ← hidx]
    exact hc1
  rw [h1]
  exact chiRep_mem_Tset _ hc' w

theorem liftEquiv_symm_eq_rootSimplex (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    ((Work.MbarHomology.CellAtlas.liftEquiv Work.MbarHomology.Mbar.mbarAtlasOf n n e).symm
      ⟨s, h⟩).1 = Work.MbarHomology.Mbar.rootSimplex n hn e s := by
  have hsub : (Work.MbarHomology.CellAtlas.liftEquiv Work.MbarHomology.Mbar.mbarAtlasOf n n e).symm ⟨s, h⟩
      = ⟨Work.MbarHomology.Mbar.rootSimplex n hn e s,
          Work.MbarHomology.Mbar.carCx_rootSimplex n hn e s h⟩ := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    show s = Work.MbarHomology.Mbar.liftCx (Work.MbarHomology.Mbar.rootSimplex n hn e s)
    rw [Work.MbarHomology.Mbar.liftCx_rootSimplex n hn e s h]
  exact congrArg Subtype.val hsub

/-! ## §4  The subdivision chain of the root face, summand by summand -/

/-- The `s`-th summand of the subdivision chain of the root face of `e`, read through the inverse
of the atlas lift. -/
def sdSummand (n : ℕ) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n) :
    Work.MbarHomology.mbarSd.chainX n :=
  if h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
    Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
      (ConcreteCategory.hom (Work.MbarHomology.mbarSd.chainι n
        ((Work.MbarHomology.CellAtlas.liftEquiv Work.MbarHomology.Mbar.mbarAtlasOf n n e).symm
          ⟨s, h⟩).1)) (1 : ℤ)
  else 0

theorem z_eq_sum_sdSummand (n : ℕ) (e : Fin (mbarDim n)) :
    Work.MbarHomology.CellAtlas.z Work.MbarHomology.Mbar.mbarAtlasOf n e
      = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n, sdSummand n e s := rfl

theorem sdSummand_pos (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    sdSummand n e s = Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
      (ConcreteCategory.hom (Work.MbarHomology.mbarSd.chainι n
        (Work.MbarHomology.Mbar.rootSimplex n hn e s))) (1 : ℤ) := by
  unfold sdSummand
  rw [dif_pos h]
  congr 1
  rw [liftEquiv_symm_eq_rootSimplex n hn e s h]

theorem sdSummand_neg (n : ℕ) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (h : ¬ s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    sdSummand n e s = 0 := by
  unfold sdSummand
  rw [dif_neg h]

/-- The `s`-th summand of `Ψ_M` of the `e`-th cell. -/
def chiSummand (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n) :
    (Work.Homology.singChain Work.Homology.ZMod (TopCat.of Work.FoldInst.Mbar)).X n :=
  if h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
    Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
      singGen (Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s))
  else 0

theorem chiSummand_pos (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    chiSummand n hn e s = Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s •
      singGen (Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s)) := by
  unfold chiSummand
  rw [dif_pos h]

theorem chiSummand_neg (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (h : ¬ s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    chiSummand n hn e s = 0 := by
  unfold chiSummand
  rw [dif_neg h]

/-! ## §5  The lift of a characteristic map of a truncation cell -/

/-- The continuous lift of the characteristic map of the root simplex `s` of `e` through the cusp
parametrisation. -/
def liftSimplex (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (hc : ∃ c : Fin 48,
      c ∈ Work.MbarHomology.qTightC (Work.MbarHomology.Mbar.rootCx n e).idx ∧ 24 ≤ c.val)
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e) :
    C(StdSimplex ℝ (Fin (n+1)), Cop) :=
  cuspInvCM.comp
    ⟨fun w => ⟨Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s) w,
        chi_rootSimplex_mem_Tset n hn e s hs hc w⟩,
      Continuous.subtype_mk
        (Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s)).continuous
        (fun w => chi_rootSimplex_mem_Tset n hn e s hs hc w)⟩

theorem cuspMap_liftSimplex_apply (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n))
    (hc : ∃ c : Fin 48,
      c ∈ Work.MbarHomology.qTightC (Work.MbarHomology.Mbar.rootCx n e).idx ∧ 24 ≤ c.val)
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n)
    (hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e)
    (w : StdSimplex ℝ (Fin (n+1))) :
    (cuspMap (liftSimplex n hn e hc s hs w) : Work.FoldInst.Mbar)
      = Work.MbarHomology.Mbar.chi n (Work.MbarHomology.Mbar.rootSimplex n hn e s) w := by
  simp only [liftSimplex, cuspInvCM, ContinuousMap.comp_apply]
  exact cuspMap_cuspInvT _

/-! ## §6  The expansion of `Ψ_M` on a basis vector -/

theorem PsiM_f_piSingle_eq_sum (n : ℕ) (hn : n < 5) (e : Fin (mbarDim n)) :
    (Work.BridgeSquare.PsiM.f n) (Pi.single e (1 : ℤ))
      = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
          chiSummand n hn e s := by
  have h1 : (Work.BridgeSquare.PsiM.f n) (Pi.single e (1 : ℤ))
      = ConcreteCategory.hom
          (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
          (Work.MbarHomology.CellAtlas.z Work.MbarHomology.Mbar.mbarAtlasOf n e) := by
    show ConcreteCategory.hom ((Work.MbarHomology.CellAtlas.zMap Work.MbarHomology.Mbar.mbarAtlasOf
          Work.MbarHomology.Mbar.mbarBoundaryCompat).f n ≫
        ((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
        (Pi.single e (1:ℤ)) = _
    rw [CategoryTheory.comp_apply]
    congr 1
    exact Work.MbarHomology.CellAtlas.zMapFun_piSingle _ _ _
  have key : ConcreteCategory.hom
        (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
        (Work.MbarHomology.CellAtlas.z Work.MbarHomology.Mbar.mbarAtlasOf n e)
      = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
          chiSummand n hn e s := by
    calc ConcreteCategory.hom
            (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
            (Work.MbarHomology.CellAtlas.z Work.MbarHomology.Mbar.mbarAtlasOf n e)
        = ConcreteCategory.hom
            (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
            (∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n, sdSummand n e s) :=
          congrArg (fun y => ConcreteCategory.hom
            (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n) y)
            (z_eq_sum_sdSummand n e)
      _ = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
            ConcreteCategory.hom
              (((Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap).deltaChainMap.f n)
              (sdSummand n e s) := map_sum _ _ _
      _ = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
            chiSummand n hn e s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          by_cases h : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e
          · rw [sdSummand_pos n hn e s h, chiSummand_pos n hn e s h]
            refine Eq.trans (map_smul _ _ _) ?_
            congr 1
            erw [← CategoryTheory.comp_apply, Work.DeltaHomology.DeltaSimplexMap.deltaChainMap_chainι]
            rfl
          · rw [sdSummand_neg n e s h, chiSummand_neg n hn e s h]
            exact map_zero _
  rw [h1, key]

/-! ## §7  The main statement -/

theorem PsiM_truncCell_mem_range (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    (h : Work.BridgeSquare.isTruncCell n e = true) :
    ∃ γ : (Work.BridgeSquare.singCxFun.obj
        (Work.BridgeSquare.Cop (rt := Work.RTOwed.rtData))).X n,
      ((Work.BridgeSquare.singCxFun.map (Work.BridgeSquare.cuspMap
          (rt := Work.RTOwed.rtData))).f n) γ
        = (Work.BridgeSquare.PsiM.f n) (Pi.single e (1 : ℤ)) := by
  by_cases hn : n < 5
  · have hc : ∃ c : Fin 48,
        c ∈ Work.MbarHomology.qTightC (Work.MbarHomology.Mbar.rootCx n e).idx ∧ 24 ≤ c.val := by
      unfold Work.BridgeSquare.isTruncCell at h
      exact of_decide_eq_true h
    refine ⟨∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
        (if hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
          (Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s) •
            singGen (liftSimplex n hn e hc s hs)
        else 0), ?_⟩
    rw [PsiM_f_piSingle_eq_sum n hn e]
    have hL : ConcreteCategory.hom
          ((Work.Homology.singChainMap Work.Homology.ZMod
            (Work.BridgeSquare.cuspMap (rt := Work.RTOwed.rtData))).f n)
          (∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
            (if hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
              (Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s) •
                singGen (liftSimplex n hn e hc s hs)
            else 0))
        = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
            chiSummand n hn e s := by
      calc ConcreteCategory.hom
              ((Work.Homology.singChainMap Work.Homology.ZMod
                (Work.BridgeSquare.cuspMap (rt := Work.RTOwed.rtData))).f n)
              (∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
                (if hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
                  (Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s) •
                    singGen (liftSimplex n hn e hc s hs)
                else 0))
          = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
              ConcreteCategory.hom
                ((Work.Homology.singChainMap Work.Homology.ZMod
                  (Work.BridgeSquare.cuspMap (rt := Work.RTOwed.rtData))).f n)
                (if hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e then
                  (Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf n e s) •
                    singGen (liftSimplex n hn e hc s hs)
                else 0) := map_sum _ _ _
        _ = ∑ s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell n,
              chiSummand n hn e s := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases hs : s (Fin.last n) = Work.MbarHomology.Mbar.rootCx n e
            · rw [dif_pos hs, chiSummand_pos n hn e s hs]
              refine Eq.trans (map_smul _ _ _) ?_
              congr 1
              rw [singGen_natural]
              congr 1
              ext w
              exact cuspMap_liftSimplex_apply n hn e hc s hs w
            · rw [dif_neg hs, chiSummand_neg n hn e s hs]
              exact map_zero _
    rw [hL]
  · have h0 : Work.HomologyIso.Gen.mbarDim n = 0 :=
      Work.HomologyIso.Gen.mbarDim_eq_zero n (by omega)
    exact Fin.elim0 (h0 ▸ e)

end

end Work.BridgeSquare
