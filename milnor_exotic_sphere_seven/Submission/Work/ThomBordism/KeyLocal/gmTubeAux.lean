import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartDefs
import Submission.Work.ThomBordism.KeyLocal.tubeCoordsFDeriv
import Submission.Work.ThomBordism.KeyLocal.gmSign
import Submission.Work.ThomBordism.KeyLocal.pairSignGauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# The ambient objects of the (GM) tube comparison

The last-mile piece (GM) compares two pullbacks of `stdModelGen (8+k)` on the chart piece
`tubeBaseSet E C ND i` of the tube: the product coordinate map
`tcmSumLin 8 k (tChartA y, b y)` and the translation `y ↦ y - E.e x`.

Both are restrictions of maps of the ambient Euclidean space `ℝ^{8+k}`, and the comparison is made
by the germ principle `KeyLocal.germPullbackEucAt` on the open set `tcfdSet E C ND i` (the open
tube over the base set of the chart `i`).  This file collects the ambient objects:

* `ambTubeProduct` — the ambient product coordinate map;
* `tcfdSet` is open (`isOpen_tcfdSet`);
* the continuity of the σ-corrected frame along the tube (`continuousOn_gframe`,
  `continuousAt_gframe_inv`);
* `tcfdIncl` — the inclusion of the open ambient piece into the chart piece;
* the punctured set of the chart piece is the point-relative set (`tubeBasePunct_eq`).
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Continuity of the σ-corrected frame -/

/-- Continuity of the σ-corrected normal frame on the base set of the chart. -/
theorem continuousOn_gframe (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (a : Fin k) :
    ContinuousOn (fun x => Work.ThomBordism.Gauss.gframe E ND i x a) (ND.D.baseSet i) := by
  have hfun : (fun x => Work.ThomBordism.Gauss.gframe E ND i x a) = fun x =>
      (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1) •
        Work.Tubular.orthFrame E ND i x a :=
    funext fun x => Work.ThomBordism.Gauss.gframe_apply E ND i x a
  rw [hfun]
  have hcoef : ContinuousOn
      (fun x => (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1))
      (ND.D.baseSet i) := by
    by_cases ha : (a : ℕ) = 0
    · rw [show (fun x => (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1)) =
        fun x => Work.ThomBordism.Gauss.sigma E ND i x from funext fun x => by rw [if_pos ha]]
      exact Work.ThomBordism.Gauss.continuousOn_sigma E ND i
    · rw [show (fun x => (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1)) =
        fun _ => (1 : ℝ) from funext fun x => by rw [if_neg ha]]
      exact continuousOn_const
  exact hcoef.smul (Work.Tubular.continuousOn_orthFrame E ND i a)

/-- Continuity of the σ-corrected frame along the tube, at an embedding point. -/
theorem continuousAt_gframe_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (a : Fin k) :
    ContinuousAt (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)) a) (E.e x) := by
  have h1 : ContinuousAt (fun y : Work.Tubular.Euc (8 + k) =>
      NormalTotal.proj (C.inv y)) (E.e x) :=
    (contMDiffOn_proj_inv E C).continuousOn.continuousAt
      (C.openTube_isOpen.mem_nhds (C.mem_openTube x))
  have h2 : ContinuousAt (fun z : V.pt => Work.ThomBordism.Gauss.gframe E ND i z a) x :=
    (continuousOn_gframe E ND i a).continuousAt ((ND.D.isOpen_baseSet i).mem_nhds hx)
  have h3 : NormalTotal.proj (C.inv (E.e x)) = x := proj_inv_embed_tcfd E C x
  exact h2.comp_of_eq h1 h3

/-! ## The ambient product coordinate map -/

/-- **The ambient product coordinate map** of the tube at the chart `i`: the composite
`ℝ^{8+k} → ℝ^8 × ℝ^k → ℝ^{8+k}` of the translated chart of the foot and of the σ-corrected reading
of the normal vector.  It is the ambient form of the product coordinate map `tcmSumMap tChartA b` of
the chart piece (`ambTubeProduct_apply_tcfdIncl`). -/
noncomputable def ambTubeProduct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    Work.Tubular.Euc (8 + k) → Work.Tubular.Euc (8 + k) :=
  fun y => Work.Whitney.tcmSumLin 8 k
    (chartMap V i.1 (NormalTotal.proj (C.inv y)) - chartMap V i.1 x,
     Work.ThomBordism.readFrame
       (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
       (NormalTotal.vec (C.inv y)))

/-- **The ambient translation** `y ↦ y - E.e x`. -/
def ambTubeShift (E : EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.Euc (8 + k) → Work.Tubular.Euc (8 + k) :=
  fun y => y - E.e x

/-! ## The open ambient piece `tcfdSet` -/

theorem isOpen_tcfdSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : IsOpen (tcfdSet E C ND i) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  exact tcfdSet_mem_nhds E C ND i hy.2 hy.1 rfl

theorem embed_mem_tcfdSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    E.e x ∈ tcfdSet E C ND i :=
  ⟨C.mem_openTube x, by
    show NormalTotal.proj (C.inv (E.e x)) ∈ ND.D.baseSet i
    rw [proj_inv_embed_tcfd E C x]; exact hx⟩

/-! ## Continuity of the ambient product coordinate map -/

theorem continuousOn_chartMap_foot (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ContinuousOn (fun y : Work.Tubular.Euc (8 + k) =>
      chartMap V i.1 (NormalTotal.proj (C.inv y))) (tcfdSet E C ND i) :=
  ((chartOf V i.1).1.continuousOn).comp
    ((contMDiffOn_proj_inv E C).continuousOn.mono (tcfdSet_sub_openTube E C ND i))
    (fun y hy => ND.baseSet_sub i.1 i.2 _ (tcfdSet_sub_baseSet E C ND i y hy))

theorem continuousOn_readFrame_foot (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ContinuousOn (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.readFrame
        (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
        (NormalTotal.vec (C.inv y))) (tcfdSet E C ND i) := by
  have hfoot : ∀ a : Fin k, ContinuousOn (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)) a)
      (tcfdSet E C ND i) := fun a =>
    (continuousOn_gframe E ND i a).comp
      ((contMDiffOn_proj_inv E C).continuousOn.mono (tcfdSet_sub_openTube E C ND i))
      (fun y hy => tcfdSet_sub_baseSet E C ND i y hy)
  have hv : ContinuousOn (fun y : Work.Tubular.Euc (8 + k) => NormalTotal.vec (C.inv y))
      (tcfdSet E C ND i) :=
    (contMDiffOn_vec_inv E C).continuousOn.mono (tcfdSet_sub_openTube E C ND i)
  have hfun : (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.readFrame
        (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
        (NormalTotal.vec (C.inv y)))
      = fun y => Work.Tubular.funToEuc k (fun a =>
          inner ℝ (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)) a)
            (NormalTotal.vec (C.inv y))) :=
    funext fun y => Work.ThomBordism.readFrame_apply _ _
  rw [hfun]
  exact ((Work.Tubular.funToEuc k).continuous.comp_continuousOn
    (continuousOn_pi.mpr fun a => (hfoot a).inner hv))

theorem continuousOn_ambTubeProduct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    ContinuousOn (ambTubeProduct E C ND i x) (tcfdSet E C ND i) :=
  (Work.Whitney.tcmSumLin 8 k).continuous.comp_continuousOn
    ((continuousOn_chartMap_foot E C ND i).sub continuousOn_const |>.prodMk
      (continuousOn_readFrame_foot E C ND i))

/-! ## The embedding point -/

/-- The embedding point, as a point of the open ambient piece. -/
def tcfdPoint (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ↥(tcfdSet E C ND i) :=
  ⟨E.e x, embed_mem_tcfdSet E C ND i x hx⟩

@[simp] theorem tcfdPoint_val (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    (tcfdPoint E C ND i x hx : Work.Tubular.Euc (8 + k)) = E.e x := rfl

theorem ambTubeProduct_zero (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ambTubeProduct E C ND i x (E.e x) = 0 := by
  have h1 : NormalTotal.proj (C.inv (E.e x)) = x := proj_inv_embed_tcfd E C x
  have h2 : NormalTotal.vec (C.inv (E.e x)) = 0 := vec_inv_embed_tcfd E C x
  show Work.Whitney.tcmSumLin 8 k
    (chartMap V i.1 (NormalTotal.proj (C.inv (E.e x))) - chartMap V i.1 x,
     Work.ThomBordism.readFrame
       (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv (E.e x))))
       (NormalTotal.vec (C.inv (E.e x)))) = 0
  simp [h1, h2]

/-! ## The inclusion of the open ambient piece into the chart piece -/

/-- **The inclusion of the open ambient piece into the chart piece.** -/
def tcfdIncl (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    C(↥(tcfdSet E C ND i), ↥(tubeBaseSet E C ND i)) :=
  ⟨fun z => ⟨⟨z.1, C.openTube_subset_U (tcfdSet_sub_openTube E C ND i z.2)⟩,
      tcfdSet_sub_baseSet E C ND i z.1 z.2⟩,
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val
        (fun z => C.openTube_subset_U (tcfdSet_sub_openTube E C ND i z.2))) _⟩

@[simp] theorem tcfdIncl_apply (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (z : ↥(tcfdSet E C ND i)) :
    ((tcfdIncl E C ND i z : ↥(tubeBaseSet E C ND i)) : Work.Tubular.Euc (8 + k)) = z.1 := rfl

/-- **The chart piece point of the embedding point.** -/
def tubePoint (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ↥(tubeBaseSet E C ND i) :=
  ⟨⟨E.e x, C.openTube_subset_U (C.mem_openTube x)⟩, by
    show NormalTotal.proj (C.inv (E.e x)) ∈ ND.D.baseSet i
    rw [proj_inv_embed_tcfd E C x]; exact hx⟩

@[simp] theorem tubePoint_val (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    (tubePoint E C ND i x hx : Work.Tubular.Euc (8 + k)) = E.e x := rfl

@[simp] theorem tcfdIncl_tcfdPoint (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    tcfdIncl E C ND i (tcfdPoint E C ND i x hx) = tubePoint E C ND i x hx := rfl

/-! ## The punctured chart piece is the point-relative set -/

/-- **The punctured set of the chart piece is the complement of the embedding point.** -/
theorem tubeBasePunct_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i
      = {y : ↥(tubeBaseSet E C ND i) | (y : Work.Tubular.Euc (8 + k)) ≠ E.e x} := by
  ext y
  constructor
  · intro hy h
    rw [Set.mem_union] at hy
    rcases hy with hy | hy
    · exact hy (by
        show NormalTotal.proj (C.inv y.1.1) = x
        rw [h, proj_inv_embed_tcfd E C x])
    · rw [mem_tubeBaseSetPunct, mem_normalNonzero] at hy
      refine hy ?_
      rw [show Work.Tubular.normalNorm E (C.inv y.1.1)
          = ‖NormalTotal.vec (C.inv y.1.1)‖ from rfl]
      rw [show NormalTotal.vec (C.inv y.1.1) = 0 by rw [h, vec_inv_embed_tcfd E C x]]
      simp
  · intro hy
    rw [Set.mem_union]
    by_cases hfoot : tubeFoot E C y.1 = x
    · right
      rw [mem_tubeBaseSetPunct, mem_normalNonzero]
      rw [show Work.Tubular.normalNorm E (C.inv y.1.1)
        = ‖NormalTotal.vec (C.inv y.1.1)‖ from rfl]
      intro hnorm
      have hv : NormalTotal.vec (C.inv y.1.1) = 0 := norm_eq_zero.mp hnorm
      have hsum : E.e (NormalTotal.proj (C.inv y.1.1)) + NormalTotal.vec (C.inv y.1.1)
          = y.1.1 := by
        have h := C.tubeMap_inv y.1.1 y.1.2
        rw [show Work.Tubular.tubeMap E (C.inv y.1.1)
          = E.e (NormalTotal.proj (C.inv y.1.1)) + NormalTotal.vec (C.inv y.1.1) from rfl] at h
        exact h
      have hfoot' : NormalTotal.proj (C.inv y.1.1) = x := hfoot
      rw [hfoot', hv, add_zero] at hsum
      exact hy hsum.symm
    · exact Or.inl hfoot

/-! ## The value of the ambient product map on the inclusion -/

/-- The ambient product coordinate map, restricted to the open piece, is the product coordinate map
of the chart piece. -/
theorem ambTubeProduct_apply_tcfdIncl (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (z : ↥(tcfdSet E C ND i)) :
    ambTubeProduct E C ND i x z.1
      = Work.Whitney.tcmSumLin 8 k
        (tChartA E C ND i x hx (tcfdIncl E C ND i z),
         tubeNormCoord E C ND i (tcfdIncl E C ND i z)) := by
  simp only [ambTubeProduct, tChartA_apply, chartTrans_apply, tubeNormCoord,
    tcfdIncl, Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.vec]
  rfl

/-- The ambient shift, restricted to the open piece, is the shift map of the chart piece. -/
theorem ambTubeShift_apply_tcfdIncl (E : EmbeddingData V (8 + k)) (x : V.pt)
    (z : Work.Tubular.Euc (8 + k)) :
    ambTubeShift E x z = z - E.e x := rfl

/-- **Nonvanishing of the ambient product map off the embedding point.** -/
theorem ambTubeProduct_ne_zero (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (b : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc k))
    (hb : ∀ y, b y = tubeNormCoord E C ND i y)
    (hmemP : ∀ y ∈ tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i,
      Work.Whitney.tcmSumLin 8 k (tChartA E C ND i x hx y, b y)
        ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
    {z : ↥(tcfdSet E C ND i)} (hz : z ≠ tcfdPoint E C ND i x hx) :
    ambTubeProduct E C ND i x z.1 ≠ 0 := by
  have hz' : z.1 ≠ E.e x := fun h => hz (Subtype.ext h)
  have hmem : tcfdIncl E C ND i z ∈ tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i := by
    rw [tubeBasePunct_eq]
    exact hz'
  have hp := hmemP (tcfdIncl E C ND i z) hmem
  rw [ambTubeProduct_apply_tcfdIncl, ← hb (tcfdIncl E C ND i z)]
  exact hp


end

end Work.ThomBordism.KeyLocal
