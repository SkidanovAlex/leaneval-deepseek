import Mathlib
import Submission.Work.ThomBordism.KeyLocal._assAux
import Submission.Work.ThomBordism.KeyLocal.tubeTanReadingO
import Submission.Work.ThomBordism.KeyLocal.exists_tubeNormCoordMap
import Submission.Work.ThomBordism.KeyLocal.chartProductFormula
import Submission.Work.ThomBordism.KeyLocal.gmTubeProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem chartCompare {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (C : TubeChart E ε)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1) :
    Work.Whitney.tcmRelCup (tubeFootPunct E C ND i x) (tubeBaseSetPunct E C ND i)
        (isOpen_tubeFootPunct E C ND i x) (isOpen_tubeBaseSetPunct E C ND i) 8 k
      ((Work.Thom.relCohMap ((FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i))
          (tubeFootPunct E C ND i x) (FrameSigns.punct V x)
          (tubeFootPunct_mem_srcIncl E C ND i x) ℤ 8).hom o)
      ((Work.Thom.relCohMap (tubeBaseSetIncl E C ND i) (tubeBaseSetPunct E C ND i)
          (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ k).hom
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k))))
    = tauSign •
      (Work.Thom.relCohMap
        (⟨fun y : ↥(tubeBaseSet E C ND i) => (y : Work.Tubular.Euc (8 + k)) - E.e x,
          by fun_prop⟩ : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubePoint_ne E C ND i x hx) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := by
  classical
  obtain ⟨b, hb, hzero⟩ := exists_tubeNormCoordMap E ND C i x hx
  have hT1 := tubeTanReadingO E C ND i x hx o ho (tubeFootPunct_mem_srcIncl E C ND i x)
    (tubeFootPunct_mem_tChartA E C ND i x hx)
  have hT2 := tubeNormReading hk E ND G hgm hbp hvec C i b hb
    (tubeBaseSetPunct_mem E C ND i b hzero)
  have hPR := chartProductFormula (tChartA E C ND i x hx) b
    (tubeFootPunct E C ND i x) (tubeBaseSetPunct E C ND i)
    (isOpen_tubeFootPunct E C ND i x) (isOpen_tubeBaseSetPunct E C ND i)
    (tubeFootPunct_mem_tChartA E C ND i x hx) (tubeBaseSetPunct_mem E C ND i b hzero)
    (tubeFootPunct_eq_preimage_tChartA E C ND i x hx)
    (tubeBaseSetPunct_eq_preimage E C ND i b hzero)
    (notMem_tcmSumLin (tChartA E C ND i x hx) b _ _ (tubeFootPunct_mem_tChartA E C ND i x hx)
      (tubeBaseSetPunct_mem E C ND i b hzero))
  have hGM := gmTubeProduct hk E C ND i x hx b hb
    (notMem_tcmSumLin (tChartA E C ND i x hx) b _ _ (tubeFootPunct_mem_tChartA E C ND i x hx)
      (tubeBaseSetPunct_mem E C ND i b hzero))
    (tubePoint_ne E C ND i x hx)
  set fs : ℤ := (if 0 < FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
    then (1 : ℤ) else -1) with hfs
  have hfs2 : fs * fs = 1 := by
    rw [hfs]
    by_cases h : 0 < FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx) <;> simp [h]
  have hL :
      (Work.Whitney.tcmRelCup (tubeFootPunct E C ND i x) (tubeBaseSetPunct E C ND i)
          (isOpen_tubeFootPunct E C ND i x) (isOpen_tubeBaseSetPunct E C ND i) 8 k
        ((Work.Thom.relCohMap ((FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i))
            (tubeFootPunct E C ND i x) (FrameSigns.punct V x)
            (tubeFootPunct_mem_srcIncl E C ND i x) ℤ 8).hom o))
        ((Work.Thom.relCohMap (tubeBaseSetIncl E C ND i) (tubeBaseSetPunct E C ND i)
            (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ k).hom
          (Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.tautologicalBundle_horiO k))))
      = fs •
        ((Work.Whitney.tcmRelCup (tubeFootPunct E C ND i x) (tubeBaseSetPunct E C ND i)
            (isOpen_tubeFootPunct E C ND i x) (isOpen_tubeBaseSetPunct E C ND i) 8 k
          ((Work.Thom.relCohMap (tChartA E C ND i x hx) (tubeFootPunct E C ND i x)
              ({0}ᶜ : Set (Work.Tubular.Euc 8))
              (tubeFootPunct_mem_tChartA E C ND i x hx) ℤ 8).hom
            FrameSigns.tau))
          ((Work.Thom.relCohMap b (tubeBaseSetPunct E C ND i)
              ({0}ᶜ : Set (Work.Tubular.Euc k))
              (tubeBaseSetPunct_mem E C ND i b hzero) ℤ k).hom
            (Work.ThomBordism.stdModelGen k))) := by
    rw [hT1, hT2, map_zsmul]
    rfl
  have hGMZ :
      (Work.Thom.relCohMap
        (⟨fun y => Work.Whitney.tcmSumLin 8 k (tChartA E C ND i x hx y, b y),
          (Work.Whitney.tcmSumLin 8 k).continuous.comp
            ((tChartA E C ND i x hx).continuous.prodMk b.continuous)⟩ :
          C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        (notMem_tcmSumLin (tChartA E C ND i x hx) b (tubeFootPunct E C ND i x)
          (tubeBaseSetPunct E C ND i) (tubeFootPunct_mem_tChartA E C ND i x hx)
          (tubeBaseSetPunct_mem E C ND i b hzero)) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))
      = fs •
        (Work.Thom.relCohMap
          (⟨fun y : ↥(tubeBaseSet E C ND i) => (y : Work.Tubular.Euc (8 + k)) - E.e x,
            by fun_prop⟩ : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
          (tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubePoint_ne E C ND i x hx) ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) := hGM
  rw [hL, hPR, hGMZ, smul_smul, smul_smul]
  congr 1
  calc fs * tauSign * fs = tauSign * (fs * fs) := by ring
    _ = tauSign := by rw [hfs2, mul_one]

end

end Work.ThomBordism.KeyLocal
