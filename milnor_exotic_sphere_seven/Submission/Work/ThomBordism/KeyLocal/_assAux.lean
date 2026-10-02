import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartDefs
import Submission.Work.ThomBordism.KeyLocal.tubeNormReading
import Submission.Work.ThomBordism.ambientClassDefs

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

/-- The inclusion of the chart piece into the closed tube. -/
def tubeBaseIncl (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : C(↥(tubeBaseSet E C ND i), ↥C.U) :=
  ⟨fun y => y.1, continuous_subtype_val⟩

@[simp] theorem tubeBaseIncl_apply (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    tubeBaseIncl E C ND i y = y.1 := rfl

theorem tubeFootPunct_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    tubeFootPunct E C ND i x
      = (fun y : ↥(tubeBaseSet E C ND i) => tubeFoot E C (tubeBaseIncl E C ND i y))
        ⁻¹' ({x}ᶜ : Set V.pt) := rfl

theorem isOpen_tubeFootPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    IsOpen (tubeFootPunct E C ND i x) := by
  rw [tubeFootPunct_eq]
  exact isClosed_singleton.isOpen_compl.preimage
    ((tubeFoot E C).continuous.comp (tubeBaseIncl E C ND i).continuous)

theorem tubeBaseSetPunct_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    tubeBaseSetPunct E C ND i
      = (fun y : ↥(tubeBaseSet E C ND i) => C.inv (tubeBaseIncl E C ND i y).1)
        ⁻¹' normalNonzero E := rfl

theorem isOpen_tubeBaseSetPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    IsOpen (tubeBaseSetPunct E C ND i) := by
  rw [tubeBaseSetPunct_eq]
  exact (isOpen_normalNonzero E).preimage
    (C.continuousOn_inv.comp_continuous
      (continuous_subtype_val.comp (tubeBaseIncl E C ND i).continuous)
      (fun y => (tubeBaseIncl E C ND i y).2))

theorem isOpen_tubeBaseSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    IsOpen (tubeBaseSet E C ND i) := by
  have h : tubeBaseSet E C ND i
      = tubeFoot E C ⁻¹' (ND.D.baseSet i) := rfl
  rw [h]
  exact (ND.D.isOpen_baseSet i).preimage (tubeFoot E C).continuous

theorem zeroSectionNormal_notMem_normalNonzero (E : EmbeddingData V (8 + k)) (x : V.pt) :
    zeroSectionNormal E x ∉ normalNonzero E := by
  rw [mem_normalNonzero]
  rw [zeroSectionNormal_apply, normalNorm_mk, norm_zero]
  exact fun h => h rfl

theorem mem_tubeBaseSet_embed (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U) ∈ tubeBaseSet E C ND i ↔ x ∈ ND.D.baseSet i := by
  rw [mem_tubeBaseSet, inv_embed E C x, zeroSectionNormal_proj]

end

end Work.ThomBordism.KeyLocal

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem chartMap_injOn (V : Work.ThomBordism.Man8) (i : ChartIdx V) :
    ∀ a ∈ src V i, ∀ b ∈ src V i, chartMap V i a = chartMap V i b → a = b := by
  intro a ha b hb h
  have h1 : a = (chartOf V i).1.symm (chartMap V i a) := ((chartOf V i).1.left_inv ha).symm
  have h2 : (chartOf V i).1.symm (chartMap V i b) = b := (chartOf V i).1.left_inv hb
  rw [h1, h, h2]

theorem tChartA_eq_zero_iff (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (y : ↥(tubeBaseSet E C ND i)) :
    tChartA E C ND i x hx y = 0 ↔ tubeFoot E C (tubeBaseIncl E C ND i y) = x := by
  have hxS : x ∈ src V i.1 := ND.baseSet_sub i.1 i.2 x hx
  have hyS : tubeFoot E C (tubeBaseIncl E C ND i y) ∈ src V i.1 :=
    ND.baseSet_sub i.1 i.2 _ y.2
  constructor
  · intro h
    have h' : chartMap V i.1 (tubeFoot E C (tubeBaseIncl E C ND i y)) - chartMap V i.1 x = 0 := h
    exact chartMap_injOn V i.1 _ hyS _ hxS (sub_eq_zero.mp h')
  · intro h
    show chartMap V i.1 (tubeFoot E C (tubeBaseIncl E C ND i y)) - chartMap V i.1 x = 0
    rw [h, sub_self]

end

end Work.ThomBordism.KeyLocal

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem tubeFootPunct_mem_srcIncl (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    ∀ y ∈ tubeFootPunct E C ND i x,
      (FrameSigns.srcIncl V i.1) (tubeFootSrc E C ND i y) ∈ FrameSigns.punct V x :=
  fun y hy => FrameSigns.punctSrc_mem V i.1 x _ (tubeFootSrc_mem E C ND i y hy)

theorem tubeFootPunct_mem_tChartA (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ∀ y ∈ tubeFootPunct E C ND i x, tChartA E C ND i x hx y ∈ FrameSigns.E8p :=
  fun y hy => FrameSigns.chartTrans_mem V i.1 x (ND.baseSet_sub i.1 i.2 x hx) _
    (tubeFootSrc_mem E C ND i y hy)

theorem tubeFootPunct_eq_preimage_tChartA (E : EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i) :
    tubeFootPunct E C ND i x
      = (fun y : ↥(tubeBaseSet E C ND i) => tChartA E C ND i x hx y) ⁻¹'
          ({0}ᶜ : Set (Work.Tubular.Euc 8)) := by
  ext y
  show tubeFoot E C (tubeBaseIncl E C ND i y) ≠ x ↔ tChartA E C ND i x hx y ≠ 0
  exact ((tChartA_eq_zero_iff E C ND i x hx y).symm).not

theorem tubeBaseSetPunct_eq_preimage (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k)
    (b : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc k))
    (hzero : ∀ y, b y = 0 ↔ C.inv (tubeBaseIncl E C ND i y).1 ∉ normalNonzero E) :
    tubeBaseSetPunct E C ND i
      = (fun y : ↥(tubeBaseSet E C ND i) => b y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc k)) := by
  ext y
  show C.inv (tubeBaseIncl E C ND i y).1 ∈ normalNonzero E ↔ b y ≠ 0
  exact ⟨fun h hb => (hzero y).mp hb h, fun h => by
    by_contra hc
    exact h ((hzero y).mpr hc)⟩

theorem tubeBaseSetPunct_mem (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k)
    (b : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc k))
    (hzero : ∀ y, b y = 0 ↔ C.inv (tubeBaseIncl E C ND i y).1 ∉ normalNonzero E) :
    ∀ y ∈ tubeBaseSetPunct E C ND i, b y ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  exact ((hzero y).mp h) hy

/-- The chart-piece point over `x`. -/
def tubeChartPt (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ↥(tubeBaseSet E C ND i) :=
  ⟨⟨E.e x, C.zero_mem_U x⟩, (mem_tubeBaseSet_embed E C ND i x).mpr hx⟩

theorem tubeFoot_tubeChartPt (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    tubeFoot E C (tubeBaseIncl E C ND i (tubeChartPt E C ND i x hx)) = x := by
  show tubeFoot E C (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U) = x
  rw [tubeFoot_apply, inv_embed E C x, zeroSectionNormal_proj]

theorem tubeChartPt_notMem (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    tubeChartPt E C ND i x hx ∉ tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i := by
  intro h
  rcases h with h | h
  · exact h (tubeFoot_tubeChartPt E C ND i x hx)
  · have h' : C.inv (E.e x) ∈ normalNonzero E := h
    rw [inv_embed E C x] at h'
    exact zeroSectionNormal_notMem_normalNonzero E x h'

theorem mem_of_ne_tubeChartPt (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    {y : ↥(tubeBaseSet E C ND i)}
    (hy : y ∈ tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i) :
    (y : Work.Tubular.Euc (8 + k)) ≠ E.e x := by
  intro h0
  refine tubeChartPt_notMem E C ND i x hx ?_
  have hyU : (y : ↥C.U) = (tubeChartPt E C ND i x hx : ↥C.U) := Subtype.ext h0
  have hy' : y = tubeChartPt E C ND i x hx := Subtype.ext hyU
  rwa [hy'] at hy

theorem tubePoint_ne (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ∀ y ∈ tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i,
      (y : Work.Tubular.Euc (8 + k)) - E.e x ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact sub_ne_zero.mpr (mem_of_ne_tubeChartPt E C ND i x hx hy)

theorem notMem_tcmSumLin {X : Type} [TopologicalSpace X] {k : ℕ}
    (a : C(X, Work.Tubular.Euc 8)) (b : C(X, Work.Tubular.Euc k)) (A B : Set X)
    (hA : ∀ y ∈ A, a y ∈ ({0}ᶜ : Set (Work.Tubular.Euc 8)))
    (hB : ∀ y ∈ B, b y ∈ ({0}ᶜ : Set (Work.Tubular.Euc k))) :
    ∀ y ∈ A ∪ B, Work.Whitney.tcmSumLin 8 k (a y, b y)
      ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h0
  have h1 : (a y, b y) = (0, 0) := (Work.Whitney.tcmSumLin 8 k).injective
    (h0.trans (map_zero (Work.Whitney.tcmSumLin 8 k)).symm)
  rcases hy with hy | hy
  · exact (hA y hy) (congrArg Prod.fst h1)
  · exact (hB y hy) (congrArg Prod.snd h1)

end

end Work.ThomBordism.KeyLocal
