import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartDefs
import Submission.Work.ThomBordism.KeyLocal.gmTubeAux
import Submission.Work.ThomBordism.KeyLocal.gmTubeProductAux
import Submission.Work.ThomBordism.KeyLocal.germPullbackEucAt
import Submission.Work.ThomBordism.KeyLocal.gmSign
import Submission.Work.ThomBordism.KeyLocal.tubeCoordsFDeriv
import Submission.Work.ThomBordism.KeyLocal.pairSignGauss
import Submission.Work.ThomBordism.KeyLocal.tubeNormReading
import Submission.Work.ThomBordism.KeyLocal.pointLocalisation
import Submission.Work.ThomBordism.someOpen_relCohMap_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.KeyLocal

theorem gmTubeProduct {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (b : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc k))
    (hb : ∀ y, b y = Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y)
    (hmemP : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i,
      Work.Whitney.tcmSumLin 8 k (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx y, b y)
        ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
    (hmemT : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i,
      (y : Work.Tubular.Euc (8 + k)) - E.e x ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) :
    (Work.Thom.relCohMap
        (Work.ThomBordism.KeyLocal.tcmSumMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx) b)
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
          ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemP ℤ (8 + k)).hom
      (Work.ThomBordism.stdModelGen (8 + k))
    = (if 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
        then (1 : ℤ) else -1) •
      (Work.Thom.relCohMap
        (⟨fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
            (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
          C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
          ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemT ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := by
  classical
  obtain ⟨L, hdF, hbijL, hsignL⟩ := hasFDerivAt_ambTubeProduct hk E C ND i x hx
  set s0 : ℤ := (if 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x
    (ND.baseSet_sub i.1 i.2 x hx) then (1 : ℤ) else -1) with hs0
  -- the auxiliary maps on the open piece
  set Fm : C(↥(tcfdSet E C ND i), Work.Tubular.Euc (8 + k)) :=
    ⟨fun z => ambTubeProduct E C ND i x z,
      continuousOn_iff_continuous_domRestrict.mp (continuousOn_ambTubeProduct E C ND i x)⟩ with hFm
  set Sm : C(↥(tcfdSet E C ND i), Work.Tubular.Euc (8 + k)) :=
    ⟨fun z => (z : Work.Tubular.Euc (8 + k)) - E.e x,
      continuousOn_iff_continuous_domRestrict.mp (continuousOn_id.sub continuousOn_const)⟩ with hSm
  -- non-vanishing on the punctured open piece
  have hFnz : ∀ z ∈ tcfdSet E C ND i, z ≠ E.e x → ambTubeProduct E C ND i x z ≠ 0 := by
    intro z hz hzne
    exact ambTubeProduct_ne_zero E C ND i x hx b hb hmemP (z := ⟨z, hz⟩)
      (fun hcon => hzne (congrArg Subtype.val hcon))
  have hSnz : ∀ z ∈ tcfdSet E C ND i, z ≠ E.e x → z - E.e x ≠ 0 := by
    intro z hz hzne
    exact sub_ne_zero.mpr hzne
  have hmemF : ∀ z ∈ {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x},
      Fm z ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun z hz => hFnz z z.2 hz
  have hmemS : ∀ z ∈ {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x},
      Sm z ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun z hz => hSnz z z.2 hz
  -- the germ comparison
  have hgerm := germPullbackEucAt (n := 8 + k) (by omega)
    (isOpen_tcfdSet E C ND i) (embed_mem_tcfdSet E C ND i x hx)
    (ambTubeProduct E C ND i x) (fun z => z - E.e x)
    (continuousOn_ambTubeProduct E C ND i x) (continuousOn_id.sub continuousOn_const)
    (ambTubeProduct_zero E C ND i x hx) (sub_self (E.e x))
    hFnz hSnz L (1 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k))
    hbijL (by exact ⟨fun a b h => by simpa using h, fun b => ⟨b, by simp⟩⟩)
    hdF ((hasFDerivAt_id (E.e x)).sub_const (E.e x))
    (by
      intro h0
      have h2 : Real.sign (LinearMap.det L.toLinearMap) = 0 := by rw [h0, Real.sign_zero]
      rw [hsignL] at h2
      rcases FrameSigns.frameSign_eq_one_or_neg_one V i.1 x with h1 | h1 <;>
        rw [h1] at h2 <;> norm_num at h2)
    (by
      rw [ContinuousLinearMap.toLinearMap_one]
      simp [LinearMap.det_id])
    (Work.ThomBordism.stdModelGen (8 + k))
  -- the multiplier, expressed through the frame sign
  have hMdet : LinearMap.det
      ((1 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k))).toLinearMap = 1 := by
    rw [ContinuousLinearMap.toLinearMap_one]
    simp [LinearMap.det_id]
  have h1sign : Real.sign (LinearMap.det L.toLinearMap)
      = (if 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
          then (1 : ℝ) else -1) := by
    rw [hsignL, FrameSigns.frameSign_of_mem V i.1 x (ND.baseSet_sub i.1 i.2 x hx)]
  have hpos : (0 < LinearMap.det L.toLinearMap)
      ↔ (0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)) := by
    constructor
    · intro h
      have h2 : Real.sign (LinearMap.det L.toLinearMap) = 1 := Real.sign_of_pos h
      rw [h1sign] at h2
      by_contra hc
      rw [if_neg hc] at h2
      norm_num at h2
    · intro h
      have h2 : Real.sign (LinearMap.det L.toLinearMap) = 1 := by rw [h1sign, if_pos h]
      rcases lt_trichotomy (LinearMap.det L.toLinearMap) 0 with h3 | h3 | h3
      · rw [Real.sign_of_neg h3] at h2
        norm_num at h2
      · rw [h3, Real.sign_zero] at h2
        norm_num at h2
      · exact h3
  have hmult : ((if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1)
      * (if 0 < LinearMap.det
          ((1 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k))).toLinearMap
        then (1 : ℤ) else -1)) = s0 := by
    rw [hMdet]
    have h1 : (if (0 : ℝ) < 1 then (1 : ℤ) else -1) = 1 := by norm_num
    rw [h1, mul_one]
    rw [hs0]
    by_cases h : 0 < Work.ThomBordism.FrameSigns.pairVal V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
    · rw [if_pos (hpos.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hpos.mp hh)), if_neg h]
  -- the injectivity of the inclusion and the two transport steps
  have hinj := tcfdIncl_relative_injective E C ND i x hx
  have hinc : ∀ z ∈ ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}),
      tcfdIncl E C ND i z ∈ (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) :=
    fun z hz => by rw [tubeBasePunct_eq]; exact hz
  have hAeq : (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
      ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
      = {y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) |
          (y : Work.Tubular.Euc (8 + k)) ≠ E.e x} := tubeBasePunct_eq E C ND i x
  have hcPhi : ∀ z ∈ ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}),
      Work.ThomBordism.KeyLocal.tcmSumMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx) b
        (tcfdIncl E C ND i z) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun z hz => hmemP (tcfdIncl E C ND i z) (hinc z hz)
  have hcT : ∀ z ∈ ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}),
      (⟨fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
          (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
        C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (tcfdIncl E C ND i z) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun z hz => hmemT (tcfdIncl E C ND i z) (hinc z hz)
  have hFeq : (Work.ThomBordism.KeyLocal.tcmSumMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx) b).comp
      (tcfdIncl E C ND i) = Fm := by
    apply ContinuousMap.ext
    intro z
    show Work.Whitney.tcmSumLin 8 k
        (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx (tcfdIncl E C ND i z),
          b (tcfdIncl E C ND i z))
      = Work.Whitney.tcmSumLin 8 k
        (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx (tcfdIncl E C ND i z),
          tubeNormCoord E C ND i (tcfdIncl E C ND i z))
    rw [hb (tcfdIncl E C ND i z)]
  have hSeq : (⟨fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
        (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
      C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k))).comp
      (tcfdIncl E C ND i) = Sm := by
    apply ContinuousMap.ext
    intro z
    rfl
  apply hinj
  rw [map_zsmul]
  rw [show (Work.Thom.relCohMap (tcfdIncl E C ND i)
      ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
      (fun z hz => by rw [tubeBasePunct_eq]; exact hz) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap
        (Work.ThomBordism.KeyLocal.tcmSumMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx) b)
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
          ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemP ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)))
      = (Work.Thom.relCohMap Fm
          ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemF ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) from by
    rw [Work.Thom.relCohMap_compA_apply
      ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tcfdIncl E C ND i)
      (Work.ThomBordism.KeyLocal.tcmSumMap (Work.ThomBordism.KeyLocal.tChartA E C ND i x hx) b)
      hinc hmemP hcPhi ℤ (8 + k) (Work.ThomBordism.stdModelGen (8 + k))]
    exact congrArg (fun φ => φ.hom (Work.ThomBordism.stdModelGen (8 + k)))
      (Work.Thom.relCohMap_congrA _ _ hFeq hcPhi hmemF ℤ (8 + k))]
  rw [show (Work.Thom.relCohMap (tcfdIncl E C ND i)
      ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
      (fun z hz => by rw [tubeBasePunct_eq]; exact hz) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap
        (⟨fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
            (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
          C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
          ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemT ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)))
      = (Work.Thom.relCohMap Sm
          ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemS ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) from by
    rw [Work.Thom.relCohMap_compA_apply
      ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      (Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tcfdIncl E C ND i)
      (⟨fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
          (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
        C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
      hinc hmemT hcT ℤ (8 + k) (Work.ThomBordism.stdModelGen (8 + k))]
    exact congrArg (fun φ => φ.hom (Work.ThomBordism.stdModelGen (8 + k)))
      (Work.Thom.relCohMap_congrA _ _ hSeq hcT hmemS ℤ (8 + k))]
  rw [hgerm, hmult]


end Work.ThomBordism.KeyLocal
