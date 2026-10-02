import Mathlib
import Submission.Work.ThomBordism.Grassmann.zeroComplementSum
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Openness of the two pieces of the zero complement of a Whitney sum

For complex bundle core data `A` (rank `a`) and `C` (rank `b`) over `B`, the zero complement of the
realification of the Whitney sum `A ⊕ C` is covered by the two pieces on which the first (resp. the
second) coordinate of the fibre does not vanish (`Work.ThomBordism.Grassmann.pieceFst`,
`Work.ThomBordism.Grassmann.pieceSnd`).  This module proves that both pieces are **open**, which is
the hypothesis of the Mayer–Vietoris argument that turns the vanishing of the cohomology of the
pieces and of their intersection into the vanishing of the cohomology of the whole space.

The topological content is local.  The fibre coordinates of a point of the total space of a
`VectorBundleCore` are *not* continuous functions of the point (the topology is the one for which
the local trivialisations are homeomorphisms); the pieces are nevertheless open, because on each
chart-open piece `{p | p.1.1 ∈ Z.baseSet i}` the trivialisation `Z.localTriv i` is continuous and
the coordinate of the fibre equals the (continuous) chart coordinate `(Z.localTriv i p).2`, up to
the transition function `Z.coordChange (Z.indexAt p.1.1) i p.1.1`, which is an *invertible* linear
map and therefore preserves the kernels of the two projections `fstAB`, `sndAB`
(`fstAB_coordChange_gen`, `coordChange_apply_ne_zero_iff`).  The chart-open pieces cover the total
space, so the pieces are unions of opens.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

theorem fstAB_coordChange_gen
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (i j : ι₁ × ι₂) (y : B) (v : EuclideanSpace ℂ (Fin (a + b))) :
    fstAB a b ((Work.Whitney.whitneySum A C).coordChange i j y v)
      = A.coordChange i.1 j.1 y (fstAB a b v) := by
  rw [Work.Whitney.whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap']
  rw [sumFibreC_symm_apply a b v]
  simp [fstAB_sumFibreC]

theorem coordChange_apply_ne_zero_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {B : Type*} [TopologicalSpace B] {ι : Type*}
    (Z : VectorBundleCore 𝕜 B F ι) {i j : ι} {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) (u : F) :
    Z.coordChange i j x u ≠ 0 ↔ u ≠ 0 := by
  constructor
  · intro h hu
    apply h
    rw [hu, map_zero]
  · intro h h0
    have hcomp := Z.coordChange_comp i j i x ⟨hx, hx.1⟩ u
    rw [Z.coordChange_self i x hx.1 u] at hcomp
    rw [h0, map_zero] at hcomp
    exact h hcomp.symm

variable (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
  (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)

/-- The chart pieces. -/
def pieceChartSet (i : ι₁ × ι₂) : Set ↥(Work.Thom.zeroComplement
    (Work.Thom.realification (Work.Whitney.whitneySum A C))) :=
  {p | p.1.1 ∈ (Work.Thom.realification (Work.Whitney.whitneySum A C)).baseSet i}

theorem isOpen_pieceChartSet (i : ι₁ × ι₂) : IsOpen (pieceChartSet A C i) := by
  have hcoe : Continuous (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (p.1 : (Work.Thom.realification (Work.Whitney.whitneySum A C)).TotalSpace)) :=
    continuous_subtype_val
  have hset : pieceChartSet A C i = (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (p.1 : (Work.Thom.realification (Work.Whitney.whitneySum A C)).TotalSpace)) ⁻¹'
      ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i).source := by
    ext p
    simp only [pieceChartSet, Set.mem_setOf_eq, Set.mem_preimage]
    rw [VectorBundleCore.mem_localTriv_source]
  rw [hset]
  exact ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i).open_source.preimage hcoe

theorem pieceChartCoord_eq (i : ι₁ × ι₂)
    (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C)))) :
    fstAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)
      = A.coordChange ((Work.Whitney.whitneySum A C).indexAt p.1.1).1 i.1 p.1.1
          (fstAB a b p.1.2) := by
  have h1 : (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1)).2
      = (Work.Thom.realification (Work.Whitney.whitneySum A C)).coordChange
          ((Work.Thom.realification (Work.Whitney.whitneySum A C)).indexAt p.1.1) i p.1.1
          p.1.2 := rfl
  rw [h1, Work.Thom.realification_indexAt]
  simp only [Work.Thom.realification_coordChange]
  exact fstAB_coordChange_gen A C ((Work.Whitney.whitneySum A C).indexAt p.1.1) i p.1.1 p.1.2

theorem pieceChartCoord_ne_zero_iff (i : ι₁ × ι₂)
    (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C))))
    (hp : p ∈ pieceChartSet A C i) :
    fstAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2) ≠ 0
      ↔ fstAB a b p.1.2 ≠ 0 := by
  rw [pieceChartCoord_eq A C i p]
  refine coordChange_apply_ne_zero_iff A ?_ (fstAB a b p.1.2)
  have hp1 : p.1.1 ∈ (Work.Whitney.whitneySum A C).baseSet i := by
    simpa only [pieceChartSet, Set.mem_setOf_eq, Work.Thom.realification_baseSet] using hp
  have hp2 : p.1.1 ∈ (Work.Whitney.whitneySum A C).baseSet
      ((Work.Whitney.whitneySum A C).indexAt p.1.1) := by
    rw [← Work.Thom.realification_baseSet (Work.Whitney.whitneySum A C),
      ← Work.Thom.realification_indexAt (Work.Whitney.whitneySum A C)]
    exact (Work.Thom.realification (Work.Whitney.whitneySum A C)).mem_baseSet_at p.1.1
  rw [Work.Whitney.whitneySum_baseSet] at hp1 hp2
  exact ⟨hp2.1, hp1.1⟩


theorem sndAB_coordChange_gen
    (i j : ι₁ × ι₂) (y : B) (v : EuclideanSpace ℂ (Fin (a + b))) :
    sndAB a b ((Work.Whitney.whitneySum A C).coordChange i j y v)
      = C.coordChange i.2 j.2 y (sndAB a b v) := by
  rw [Work.Whitney.whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap']
  rw [sumFibreC_symm_apply a b v]
  simp [sndAB_sumFibreC]

theorem pieceChartCoord_eq_snd (i : ι₁ × ι₂)
    (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C)))) :
    sndAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)
      = C.coordChange ((Work.Whitney.whitneySum A C).indexAt p.1.1).2 i.2 p.1.1
          (sndAB a b p.1.2) := by
  have h1 : (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1)).2
      = (Work.Thom.realification (Work.Whitney.whitneySum A C)).coordChange
          ((Work.Thom.realification (Work.Whitney.whitneySum A C)).indexAt p.1.1) i p.1.1
          p.1.2 := rfl
  rw [h1, Work.Thom.realification_indexAt]
  simp only [Work.Thom.realification_coordChange]
  exact sndAB_coordChange_gen A C ((Work.Whitney.whitneySum A C).indexAt p.1.1) i p.1.1 p.1.2

theorem pieceChartCoord_ne_zero_iff_snd (i : ι₁ × ι₂)
    (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C))))
    (hp : p ∈ pieceChartSet A C i) :
    sndAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2) ≠ 0
      ↔ sndAB a b p.1.2 ≠ 0 := by
  rw [pieceChartCoord_eq_snd A C i p]
  refine coordChange_apply_ne_zero_iff C ?_ (sndAB a b p.1.2)
  have hp1 : p.1.1 ∈ (Work.Whitney.whitneySum A C).baseSet i := by
    simpa only [pieceChartSet, Set.mem_setOf_eq, Work.Thom.realification_baseSet] using hp
  have hp2 : p.1.1 ∈ (Work.Whitney.whitneySum A C).baseSet
      ((Work.Whitney.whitneySum A C).indexAt p.1.1) := by
    rw [← Work.Thom.realification_baseSet (Work.Whitney.whitneySum A C),
      ← Work.Thom.realification_indexAt (Work.Whitney.whitneySum A C)]
    exact (Work.Thom.realification (Work.Whitney.whitneySum A C)).mem_baseSet_at p.1.1
  rw [Work.Whitney.whitneySum_baseSet] at hp1 hp2
  exact ⟨hp2.2, hp1.2⟩

theorem isOpen_pieceChartSet_inter_pieceFst (i : ι₁ × ι₂) :
    IsOpen (pieceChartSet A C i ∩ pieceFst A C) := by
  have hcoe : Continuous (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (p.1 : (Work.Thom.realification (Work.Whitney.whitneySum A C)).TotalSpace)) :=
    continuous_subtype_val
  have hchart : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1)
      (pieceChartSet A C i) :=
    ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i).continuousOn_toFun.comp
      hcoe.continuousOn (fun p hp => hp)
  have hcoord : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)
      (pieceChartSet A C i) :=
    continuous_snd.comp_continuousOn hchart
  have hg : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      fstAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2))
      (pieceChartSet A C i) :=
    (fstAB a b).continuous.comp_continuousOn hcoord
  have hopen := hg.isOpen_inter_preimage (isOpen_pieceChartSet A C i)
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (EuclideanSpace ℂ (Fin a))))
  have hset : pieceChartSet A C i ∩ (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      fstAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)) ⁻¹'
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin a))) = pieceChartSet A C i ∩ pieceFst A C := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [mem_pieceFst]
    constructor
    · rintro ⟨hp, hf⟩
      exact ⟨hp, (pieceChartCoord_ne_zero_iff A C i p hp).mp hf⟩
    · rintro ⟨hp, hf⟩
      exact ⟨hp, (pieceChartCoord_ne_zero_iff A C i p hp).mpr hf⟩
  rw [← hset]
  exact hopen

theorem isOpen_pieceChartSet_inter_pieceSnd (i : ι₁ × ι₂) :
    IsOpen (pieceChartSet A C i ∩ pieceSnd A C) := by
  have hcoe : Continuous (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (p.1 : (Work.Thom.realification (Work.Whitney.whitneySum A C)).TotalSpace)) :=
    continuous_subtype_val
  have hchart : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      (Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1)
      (pieceChartSet A C i) :=
    ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i).continuousOn_toFun.comp
      hcoe.continuousOn (fun p hp => hp)
  have hcoord : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      ((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)
      (pieceChartSet A C i) :=
    continuous_snd.comp_continuousOn hchart
  have hg : ContinuousOn (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      sndAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2))
      (pieceChartSet A C i) :=
    (sndAB a b).continuous.comp_continuousOn hcoord
  have hopen := hg.isOpen_inter_preimage (isOpen_pieceChartSet A C i)
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (EuclideanSpace ℂ (Fin b))))
  have hset : pieceChartSet A C i ∩ (fun p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification (Work.Whitney.whitneySum A C))) =>
      sndAB a b (((Work.Thom.realification (Work.Whitney.whitneySum A C)).localTriv i p.1).2)) ⁻¹'
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin b))) = pieceChartSet A C i ∩ pieceSnd A C := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [mem_pieceSnd]
    constructor
    · rintro ⟨hp, hf⟩
      exact ⟨hp, (pieceChartCoord_ne_zero_iff_snd A C i p hp).mp hf⟩
    · rintro ⟨hp, hf⟩
      exact ⟨hp, (pieceChartCoord_ne_zero_iff_snd A C i p hp).mpr hf⟩
  rw [← hset]
  exact hopen

theorem isOpen_pieceFst_aux : IsOpen (pieceFst A C) := by
  have hunion : pieceFst A C = ⋃ i, (pieceChartSet A C i ∩ pieceFst A C) := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iUnion.mpr ⟨(Work.Thom.realification
          (Work.Whitney.whitneySum A C)).indexAt p.1.1, ?_, hp⟩
      exact (Work.Thom.realification (Work.Whitney.whitneySum A C)).mem_baseSet_at p.1.1
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨i, -, h2⟩
      exact h2
  rw [hunion]
  exact isOpen_iUnion fun i => isOpen_pieceChartSet_inter_pieceFst A C i

theorem isOpen_pieceSnd_aux : IsOpen (pieceSnd A C) := by
  have hunion : pieceSnd A C = ⋃ i, (pieceChartSet A C i ∩ pieceSnd A C) := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iUnion.mpr ⟨(Work.Thom.realification
          (Work.Whitney.whitneySum A C)).indexAt p.1.1, ?_, hp⟩
      exact (Work.Thom.realification (Work.Whitney.whitneySum A C)).mem_baseSet_at p.1.1
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨i, -, h2⟩
      exact h2
  rw [hunion]
  exact isOpen_iUnion fun i => isOpen_pieceChartSet_inter_pieceSnd A C i

theorem isOpen_pieceFst_pieceSnd
    {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    IsOpen (Work.ThomBordism.Grassmann.pieceFst A C) ∧
      IsOpen (Work.ThomBordism.Grassmann.pieceSnd A C) :=
  ⟨isOpen_pieceFst_aux A C, isOpen_pieceSnd_aux A C⟩

end

end Work.ThomBordism.Grassmann
