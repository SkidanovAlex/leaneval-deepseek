/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.Collar

/-!
# `stepGlue` is a quotient map

We prove that the canonical map
`stepGlue C n : Xₙ ⊔ ⊔ collars → stepCollar C n` of `Submission.Work.CWTOP.Basic` is a quotient
map: the topology on the collar space `stepCollar C n` is the final topology of the closed cover by
the `n`-skeleton and the collar pieces of the top cells.

The proof has three parts.

* The geometry of one top cell: `stepCollar` meets the closed cell of a top cell exactly in its
  collar piece, and the closed cell is the disjoint union of that collar piece and the inner closed
  disk of radius `1/2` (`closedCell_inter_stepCollar`, `closedCell_sdiff_collarPiece`).
* A closed ball parametrises a closed cell and is compact, so the characteristic map is a quotient
  map on it; this is what turns a statement about the model collar into a statement about points of
  `X` (`isClosed_of_isClosed_cellBallMap_preimage`).
* The assembly: a set `Ψ ⊆ stepCollar C n` whose intersection with the `n`-skeleton is closed there
  and whose pullback to every model collar is closed is the trace of a closed set of `X`
  (`exists_isClosed_stepCollar_inter`).
-/

noncomputable section

open Set Topology Metric

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

section Geom

variable {n : ℕ}

/-- A point of the closed model ball whose image in the `(n+1)`-cell `i` lies in the `n`-skeleton
has norm one. -/
lemma norm_eq_one_of_map_mem_skel_of_closedBall (i : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) i y ∈ skel C n) : ‖y‖ = 1 := by
  by_contra hne
  have hle : ‖y‖ ≤ 1 := by
    have h' := Metric.mem_closedBall.mp hy
    rwa [dist_eq_norm, sub_zero] at h'
  have hlt : ‖y‖ < 1 := lt_of_le_of_ne hle hne
  have hball : y ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt
  have hmem : RelCWComplex.map (n + 1) i y ∈ RelCWComplex.openCell (n + 1) i := ⟨y, hball, rfl⟩
  have hd := RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1)
    (j := i) (by exact_mod_cast Nat.lt_succ_self n)
  exact Set.disjoint_left.mp hd h hmem

/-- The skeleton in dimension `a` is contained in the skeleton in dimension `b` for `a ≤ b`. -/
lemma skel_mono_aux {a b : ℕ} (h : a ≤ b) : skel C a ⊆ skel C b :=
  RelCWComplex.skeleton_mono (C := C) (by exact_mod_cast h)

/-- The `m`-skeleton is contained in the whole complex. -/
lemma skel_subset_complex_aux (m : ℕ) : skel C m ⊆ C := by
  intro x hx
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  obtain ⟨k, -, j, hj⟩ := hx
  exact RelCWComplex.openCell_subset_complex k j hj

/-- The inner disk of a top cell is disjoint from the `n`-skeleton. -/
lemma disjoint_innerDiskCell_skel (i : RelCWComplex.cell C (n + 1)) :
    Disjoint (innerDiskCell C n i) (skel C n) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact Set.disjoint_left.mp
    (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1) (j := i)
      (by exact_mod_cast Nat.lt_succ_self n)) hx2 (innerDiskCell_subset_openCell i hx1)

/-- The open cell of a top cell is disjoint from the closed cell of a different top cell. -/
lemma disjoint_openCell_closedCell {i i' : RelCWComplex.cell C (n + 1)} (h : i' ≠ i) :
    Disjoint (RelCWComplex.openCell (n + 1) i') (RelCWComplex.closedCell (n + 1) i) := by
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
  rw [Set.disjoint_union_right]
  refine ⟨?_, ?_⟩
  · exact ((RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1)
      (j := i') (by exact_mod_cast Nat.lt_succ_self n)).symm).mono_right
        (RelCWComplex.cellFrontier_subset_skeleton n i)
  · exact RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [h])

/-- The `n`-skeleton meets a closed top cell in its collar piece. -/
lemma skel_inter_closedCell_subset_collarPiece (i : RelCWComplex.cell C (n + 1)) :
    skel C n ∩ RelCWComplex.closedCell (n + 1) i ⊆ collarPiece C n i := by
  rintro x ⟨hxS, hxK⟩
  obtain ⟨y, hy, rfl⟩ := hxK
  have h1 : ‖y‖ = 1 := norm_eq_one_of_map_mem_skel_of_closedBall (C := C) i hy hxS
  exact ⟨y, ⟨by rw [h1]; norm_num, le_of_eq h1⟩, rfl⟩

/-- A point of the closed ball whose image in the `(n+1)`-cell `i` lies in the collar piece of `i`
lies in the model collar. -/
lemma mem_modelCollar_of_map_mem_collarPiece (i : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) i y ∈ collarPiece C n i) : y ∈ modelCollar n := by
  obtain ⟨y', hy', heq⟩ := h
  by_cases h1 : ‖y'‖ = 1
  · have hS : RelCWComplex.map (n + 1) i y ∈ skel C n := by
      rw [← heq]
      exact RelCWComplex.cellFrontier_subset_skeleton n i
        ⟨y', by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h1, rfl⟩
    have h2 := norm_eq_one_of_map_mem_skel_of_closedBall (C := C) i hy hS
    exact ⟨by rw [h2]; norm_num, le_of_eq h2⟩
  · have h1' : ‖y'‖ < 1 := lt_of_le_of_ne hy'.2 h1
    have hy'ball : y' ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h1'
    have hopen : RelCWComplex.map (n + 1) i y ∈ RelCWComplex.openCell (n + 1) i := by
      rw [← heq]; exact ⟨y', hy'ball, rfl⟩
    by_cases h2 : ‖y‖ = 1
    · have hS : RelCWComplex.map (n + 1) i y ∈ skel C n :=
        RelCWComplex.cellFrontier_subset_skeleton n i
          ⟨y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h2, rfl⟩
      exact absurd hopen (Set.disjoint_left.mp
        (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1) (j := i)
          (by exact_mod_cast Nat.lt_succ_self n)) hS)
    · have hle : ‖y‖ ≤ 1 := by
        have h' := Metric.mem_closedBall.mp hy
        rwa [dist_eq_norm, sub_zero] at h'
      have h2' : ‖y‖ < 1 := lt_of_le_of_ne hle h2
      have hyball : y ∈ Metric.ball 0 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h2'
      have hyeq : y = y' := (RelCWComplex.map (n + 1) i).injOn
        (by rw [RelCWComplex.source_eq]; exact hyball)
        (by rw [RelCWComplex.source_eq]; exact hy'ball) heq.symm
      rw [hyeq]; exact hy'

/-- A point of the closed ball whose image in the `(n+1)`-cell `i` lies in the inner disk of `i`
lies in the closed ball of radius `1/2`. -/
lemma mem_closedBall_half_of_map_mem_innerDiskCell (i : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) i y ∈ innerDiskCell C n i) :
    y ∈ Metric.closedBall 0 (1 / 2) := by
  obtain ⟨y', hy', heq⟩ := h
  have hy'ball : y' ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h' := Metric.mem_closedBall.mp hy'
    rw [dist_eq_norm, sub_zero] at h'
    linarith
  by_cases h2 : ‖y‖ = 1
  · have hS : RelCWComplex.map (n + 1) i y ∈ skel C n :=
      RelCWComplex.cellFrontier_subset_skeleton n i
        ⟨y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h2, rfl⟩
    have hopen : RelCWComplex.map (n + 1) i y ∈ RelCWComplex.openCell (n + 1) i := by
      rw [← heq]; exact ⟨y', hy'ball, rfl⟩
    exact absurd hopen (Set.disjoint_left.mp
      (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1) (j := i)
        (by exact_mod_cast Nat.lt_succ_self n)) hS)
  · have hle : ‖y‖ ≤ 1 := by
      have h' := Metric.mem_closedBall.mp hy
      rwa [dist_eq_norm, sub_zero] at h'
    have h2' : ‖y‖ < 1 := lt_of_le_of_ne hle h2
    have hyball : y ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h2'
    have hyeq : y = y' := (RelCWComplex.map (n + 1) i).injOn
      (by rw [RelCWComplex.source_eq]; exact hyball)
      (by rw [RelCWComplex.source_eq]; exact hy'ball) heq.symm
    rw [hyeq]
    exact hy'

/-- The closed top cell meets the collar space in the collar piece. -/
theorem closedCell_inter_stepCollar (i : RelCWComplex.cell C (n + 1)) :
    RelCWComplex.closedCell (n + 1) i ∩ stepCollar C n = collarPiece C n i := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxK, hxY⟩
    rcases mem_stepCollar.mp hxY with hxS | ⟨j, hxC⟩
    · exact skel_inter_closedCell_subset_collarPiece i ⟨hxS, hxK⟩
    · obtain ⟨y, hy, rfl⟩ := hxC
      by_cases hnorm : ‖y‖ = 1
      · have hS : RelCWComplex.map (n + 1) j y ∈ skel C n :=
          RelCWComplex.cellFrontier_subset_skeleton n j
            ⟨y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hnorm, rfl⟩
        exact skel_inter_closedCell_subset_collarPiece i ⟨hS, hxK⟩
      · have hlt : ‖y‖ < 1 := lt_of_le_of_ne hy.2 hnorm
        have hball : y ∈ Metric.ball 0 1 := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt
        have hopen : RelCWComplex.map (n + 1) j y ∈ RelCWComplex.openCell (n + 1) j :=
          ⟨y, hball, rfl⟩
        have hxK' := hxK
        rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hxK'
        rcases hxK' with hf | ho
        · exact skel_inter_closedCell_subset_collarPiece i
            ⟨RelCWComplex.cellFrontier_subset_skeleton n i hf, hxK⟩
        · have hji : j = i := by
            by_contra hne
            exact (Set.disjoint_left.mp
              (RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [hne])) hopen) ho
          subst hji
          exact ⟨y, hy, rfl⟩
  · intro x hx
    exact ⟨collarPiece_subset_closedCell i hx, collarPiece_subset_stepCollar i hx⟩

/-- The closed top cell is the disjoint union of the collar piece and the inner disk. -/
theorem closedCell_sdiff_collarPiece (i : RelCWComplex.cell C (n + 1)) :
    RelCWComplex.closedCell (n + 1) i \ collarPiece C n i = innerDiskCell C n i := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxK, hxC⟩
    obtain ⟨y, hy, rfl⟩ := hxK
    have hle : ‖y‖ ≤ 1 := by
      have h' := Metric.mem_closedBall.mp hy
      rwa [dist_eq_norm, sub_zero] at h'
    have hhalf : ‖y‖ ≤ 1 / 2 := by
      by_contra hlt
      exact hxC ⟨y, ⟨not_le.mp hlt, hle⟩, rfl⟩
    exact ⟨y, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hhalf, rfl⟩
  · intro x hx
    refine ⟨innerDiskCell_subset_closedCell i hx, ?_⟩
    rintro ⟨y, hy, hxy⟩
    obtain ⟨y', hy', rfl⟩ := hx
    by_cases h1 : ‖y‖ = 1
    · have hS : RelCWComplex.map (n + 1) i y ∈ skel C n :=
        RelCWComplex.cellFrontier_subset_skeleton n i
          ⟨y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h1, rfl⟩
      have hopen' : RelCWComplex.map (n + 1) i y' ∈ RelCWComplex.openCell (n + 1) i :=
        innerDiskCell_subset_openCell i ⟨y', hy', rfl⟩
      rw [hxy] at hS
      exact Set.disjoint_left.mp
        (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1) (j := i)
          (by exact_mod_cast Nat.lt_succ_self n)) hS hopen'
    · have h1' : ‖y‖ < 1 := lt_of_le_of_ne hy.2 h1
      have hyball : y ∈ Metric.ball 0 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h1'
      have hy'ball : y' ∈ Metric.ball 0 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have h' := Metric.mem_closedBall.mp hy'
        rw [dist_eq_norm, sub_zero] at h'
        linarith
      have hyy : y' = y := (RelCWComplex.map (n + 1) i).injOn
        (by rw [RelCWComplex.source_eq]; exact hy'ball)
        (by rw [RelCWComplex.source_eq]; exact hyball) hxy.symm
      have h' := Metric.mem_closedBall.mp hy'
      rw [dist_eq_norm, sub_zero] at h'
      exact absurd hy.1 (by rw [← hyy]; linarith)

end Geom

section CellBall

variable {n : ℕ}

/-- The parametrisation of the closed `(n+1)`-cell `i` by the closed model ball. -/
private def cellBallMap (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C (n + 1)) :
    {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 1} →
      {x : X // x ∈ RelCWComplex.closedCell (n + 1) i} :=
  fun y => ⟨RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ), (y : Fin (n + 1) → ℝ), y.2, rfl⟩

private lemma cellBallMap_continuous (C : Set X) [CWComplex C] (n : ℕ)
    (i : RelCWComplex.cell C (n + 1)) : Continuous (cellBallMap C n i) :=
  Continuous.subtype_mk
    (continuousOn_iff_continuous_restrict.mp (RelCWComplex.continuousOn (n + 1) i)) _

private lemma cellBallMap_surjective (C : Set X) [CWComplex C] (n : ℕ)
    (i : RelCWComplex.cell C (n + 1)) : Function.Surjective (cellBallMap C n i) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

private lemma isQuotientMap_cellBallMap (C : Set X) [CWComplex C] (n : ℕ)
    (i : RelCWComplex.cell C (n + 1)) : IsQuotientMap (cellBallMap C n i) := by
  refine ⟨?_, cellBallMap_surjective C n i⟩
  rw [isCoinducing_iff_isClosed]
  intro s
  refine ⟨fun hs => ?_, fun hs' => hs'.preimage (cellBallMap_continuous C n i)⟩
  haveI : CompactSpace {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 1} :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hcl : IsCompact ((cellBallMap C n i) ⁻¹' s) := IsClosed.isCompact hs
  have hcomp : IsCompact ((cellBallMap C n i) '' ((cellBallMap C n i) ⁻¹' s)) :=
    hcl.image (cellBallMap_continuous C n i)
  have himg : (cellBallMap C n i) '' ((cellBallMap C n i) ⁻¹' s) = s := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      obtain ⟨y, rfl⟩ := cellBallMap_surjective C n i x
      exact ⟨y, hx, rfl⟩
  rw [himg] at hcomp
  exact hcomp.isClosed

/-- To check that a subset of a closed top cell is closed it suffices to check its preimage in the
closed model ball. -/
private lemma isClosed_of_isClosed_cellBallMap_preimage (C : Set X) [CWComplex C] (n : ℕ)
    (i : RelCWComplex.cell C (n + 1)) {A : Set X}
    (hA : A ⊆ RelCWComplex.closedCell (n + 1) i)
    (h : IsClosed {y : {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 1} |
      RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) ∈ A}) : IsClosed A := by
  have h' : IsClosed ((cellBallMap C n i) ⁻¹' (Subtype.val ⁻¹' A)) := by
    convert h using 1
    ext y
    rfl
  have h2 : IsClosed (Subtype.val ⁻¹' A :
      Set {x : X // x ∈ RelCWComplex.closedCell (n + 1) i}) :=
    (isQuotientMap_cellBallMap C n i).isCoinducing.isClosed_preimage.mp h'
  obtain ⟨F, hF, hFs⟩ := isClosed_induced_iff.mp h2
  have hAF : A = F ∩ RelCWComplex.closedCell (n + 1) i := by
    ext x
    constructor
    · intro hx
      exact ⟨(Set.ext_iff.mp hFs ⟨x, hA hx⟩).mpr hx, hA hx⟩
    · rintro ⟨hxF, hxK⟩
      exact (Set.ext_iff.mp hFs ⟨x, hxK⟩).mp hxF
  rw [hAF]
  exact hF.inter RelCWComplex.isClosed_closedCell

end CellBall

section Assembly

variable {n : ℕ}

private lemma continuous_stepGlue_aux (C : Set X) [CWComplex C] (n : ℕ) :
    Continuous (stepGlue C n) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · exact Continuous.subtype_mk continuous_subtype_val _
  · rw [continuous_sigma_iff]
    intro i
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_iff_continuous_restrict.mp
      ((RelCWComplex.continuousOn (n + 1) i).mono collarModel_subset_closedBall)

/-- The model description of the candidate closed set on a top closed cell. -/
private lemma mem_union_iff_aux {Ψ : Set X} (hΨ : Ψ ⊆ stepCollar C n)
    {i : RelCWComplex.cell C (n + 1)} {Fb : Set (Fin (n + 1) → ℝ)}
    (hFb : ∀ y : Fin (n + 1) → ℝ, y ∈ modelCollar n →
      (y ∈ Fb ↔ RelCWComplex.map (n + 1) i y ∈ Ψ))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1) :
    (RelCWComplex.map (n + 1) i y ∈
        (Ψ ∪ ⋃ i' : RelCWComplex.cell C (n + 1), innerDiskCell C n i')
        ∧ RelCWComplex.map (n + 1) i y ∈ RelCWComplex.closedCell (n + 1) i) ↔
      y ∈ Fb ∪ Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2) := by
  have hyK : RelCWComplex.map (n + 1) i y ∈ RelCWComplex.closedCell (n + 1) i := ⟨y, hy, rfl⟩
  constructor
  · rintro ⟨hmem, -⟩
    simp only [Set.mem_union, Set.mem_iUnion] at hmem
    rcases hmem with hΨ' | ⟨i', hi'⟩
    · have hcollar : RelCWComplex.map (n + 1) i y ∈ collarPiece C n i := by
        rw [← closedCell_inter_stepCollar (C := C) (n := n) i]
        exact ⟨hyK, hΨ hΨ'⟩
      have hmodel := mem_modelCollar_of_map_mem_collarPiece (C := C) i hy hcollar
      exact Or.inl ((hFb y hmodel).mpr hΨ')
    · by_cases hii : i' = i
      · rw [hii] at hi'
        exact Or.inr (mem_closedBall_half_of_map_mem_innerDiskCell (C := C) i hy hi')
      · exact ((Set.disjoint_left.mp (disjoint_openCell_closedCell (C := C) hii)
          (innerDiskCell_subset_openCell i' hi')) hyK).elim
  · intro hmem
    refine ⟨?_, hyK⟩
    simp only [Set.mem_union] at hmem
    rcases hmem with hFb' | hhalf
    · by_cases hmodel : y ∈ modelCollar n
      · rw [Set.mem_union]
        exact Or.inl ((hFb y hmodel).mp hFb')
      · have h1 : ‖y‖ ≤ 1 := by
          have h' := Metric.mem_closedBall.mp hy
          rwa [dist_eq_norm, sub_zero] at h'
        have h2 : ¬ ((1 / 2 : ℝ) < ‖y‖) := fun hc => hmodel ⟨hc, h1⟩
        have hle : ‖y‖ ≤ 1 / 2 := not_lt.mp h2
        rw [Set.mem_union]
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨y, by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hle, rfl⟩⟩)
    · rw [Set.mem_union]
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨y, by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hhalf ⊢
        exact hhalf, rfl⟩⟩)

/-- A set `Ψ ⊆ stepCollar C n` which is closed in the `n`-skeleton and whose pullback to every
model collar is closed is the trace of a closed set of `X`. -/
private lemma exists_isClosed_stepCollar_inter {Ψ : Set X} (hΨ : Ψ ⊆ stepCollar C n)
    (hA : ∃ Fa : Set X, IsClosed Fa ∧ ∀ x : X, x ∈ skel C n → (x ∈ Fa ↔ x ∈ Ψ))
    (hB : ∀ i : RelCWComplex.cell C (n + 1),
      ∃ Fb : Set (Fin (n + 1) → ℝ), IsClosed Fb ∧
        ∀ y : Fin (n + 1) → ℝ, y ∈ modelCollar n →
          (y ∈ Fb ↔ RelCWComplex.map (n + 1) i y ∈ Ψ)) :
    ∃ G : Set X, IsClosed G ∧ G ∩ stepCollar C n = Ψ := by
  obtain ⟨Fa, hFac, hFa⟩ := hA
  choose Fb hFbc hFb using hB
  refine ⟨Ψ ∪ ⋃ i : RelCWComplex.cell C (n + 1), innerDiskCell C n i, ?_, ?_⟩
  · apply CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell (C := C)
    · -- the candidate closed set lies in the complex
      intro x hx
      simp only [Set.mem_union, Set.mem_iUnion] at hx
      rcases hx with hx | ⟨i, hx⟩
      · exact skel_subset_complex_aux (n + 1) (stepCollar_subset_skel_succ (hΨ hx))
      · exact skel_subset_complex_aux (n + 1) (innerDiskCell_subset_skel_succ i hx)
    · intro m _ i
      rcases lt_trichotomy m (n + 1) with hlt | heq | hgt
      · -- cells of dimension at most `n`
        right
        have hle : m ≤ n := by omega
        have hsub : RelCWComplex.closedCell m i ⊆ skel C n :=
          (RelCWComplex.closedCell_subset_skeleton m i).trans (skel_mono_aux hle)
        have hset : (Ψ ∪ ⋃ i' : RelCWComplex.cell C (n + 1), innerDiskCell C n i') ∩
              RelCWComplex.closedCell m i = Fa ∩ RelCWComplex.closedCell m i := by
          ext x
          constructor
          · rintro ⟨hx, hxK⟩
            simp only [Set.mem_union, Set.mem_iUnion] at hx
            rcases hx with hx | ⟨i', hx⟩
            · exact ⟨(hFa x (hsub hxK)).mpr hx, hxK⟩
            · exact (Set.disjoint_left.mp (disjoint_innerDiskCell_skel i') hx (hsub hxK)).elim
          · rintro ⟨hx, hxK⟩
            refine ⟨?_, hxK⟩
            rw [Set.mem_union]
            exact Or.inl ((hFa x (hsub hxK)).mp hx)
        rw [hset]
        exact hFac.inter RelCWComplex.isClosed_closedCell
      · -- cells of dimension `n+1`
        right
        subst heq
        apply isClosed_of_isClosed_cellBallMap_preimage (C := C) (n := n) i
        · intro x hx
          exact hx.2
        · have hset : {y : {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 1} |
              RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) ∈
                (Ψ ∪ ⋃ i' : RelCWComplex.cell C (n + 1), innerDiskCell C n i') ∩
                  RelCWComplex.closedCell (n + 1) i} =
              Subtype.val ⁻¹' (Fb i ∪ Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2)) := by
            ext y
            simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
            exact mem_union_iff_aux (C := C) (n := n) hΨ (hFb i) y.2
          rw [hset]
          exact ((hFbc i).union Metric.isClosed_closedBall).preimage continuous_subtype_val
      · -- cells of dimension bigger than `n+1`
        left
        rw [Set.disjoint_left]
        intro x hxG hxO
        have hxZ : x ∈ skel C (n + 1) := by
          simp only [Set.mem_union, Set.mem_iUnion] at hxG
          rcases hxG with hx | ⟨i', hx⟩
          · exact stepCollar_subset_skel_succ (hΨ hx)
          · exact innerDiskCell_subset_skel_succ i' hx
        exact (Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell (C := C)
          (n := ((n + 1 : ℕ) : ℕ∞)) (m := m) (j := i) (by exact_mod_cast hgt)) hxZ) hxO
  · ext x
    constructor
    · rintro ⟨hx, hxY⟩
      simp only [Set.mem_union, Set.mem_iUnion] at hx
      rcases hx with hx | ⟨i, hx⟩
      · exact hx
      · have hcollar : x ∈ collarPiece C n i := by
          rw [← closedCell_inter_stepCollar (C := C) (n := n) i]
          exact ⟨innerDiskCell_subset_closedCell i hx, hxY⟩
        have hd : x ∈ RelCWComplex.closedCell (n + 1) i \ collarPiece C n i := by
          rw [closedCell_sdiff_collarPiece (C := C) (n := n) i]
          exact hx
        exact absurd hcollar hd.2
    · intro hx
      exact ⟨Or.inl hx, hΨ hx⟩

end Assembly

theorem isQuotientMap_stepGlue {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) : Topology.IsQuotientMap (Work.CWTOP.stepGlue C n) := by
  refine ⟨?_, ?_⟩
  · rw [isCoinducing_iff_isClosed]
    intro s
    constructor
    · intro hs
      set Ψ : Set X :=
        {x | ∃ hx : x ∈ stepCollar C n, (⟨x, hx⟩ : {x : X // x ∈ stepCollar C n}) ∈ s}
        with hΨdef
      have hA : ∃ Fa : Set X, IsClosed Fa ∧ ∀ x : X, x ∈ skel C n → (x ∈ Fa ↔ x ∈ Ψ) := by
        have h1 : IsClosed (Subtype.val ⁻¹' Ψ : Set {x : X // x ∈ skel C n}) := by
          have hs1 := (isClosed_sum_iff.mp hs).1
          convert hs1 using 1
          ext x
          constructor
          · rintro ⟨h, hh⟩
            show stepGlue C n (Sum.inl x) ∈ s
            have he : stepGlue C n (Sum.inl x) =
                (⟨(x : X), h⟩ : {x : X // x ∈ stepCollar C n}) := Subtype.ext rfl
            rw [he]
            exact hh
          · intro hx
            exact ⟨Or.inl x.2, hx⟩
        obtain ⟨Fa, hFac, hFa⟩ := isClosed_induced_iff.mp h1
        exact ⟨Fa, hFac, fun x hx => by
          simpa using Set.ext_iff.mp hFa (⟨x, hx⟩ : {x : X // x ∈ skel C n})⟩
      have hB : ∀ i : RelCWComplex.cell C (n + 1),
          ∃ Fb : Set (Fin (n + 1) → ℝ), IsClosed Fb ∧
            ∀ y : Fin (n + 1) → ℝ, y ∈ modelCollar n →
              (y ∈ Fb ↔ RelCWComplex.map (n + 1) i y ∈ Ψ) := by
        intro i
        have hs2 := (isClosed_sigma_iff.mp (isClosed_sum_iff.mp hs).2) i
        have h1 : IsClosed {y : collarModel n |
            RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) ∈ Ψ} := by
          convert hs2 using 1
          ext y
          constructor
          · intro hy
            obtain ⟨hmem, hys⟩ := hy
            show stepGlue C n (Sum.inr (⟨i, y⟩ : Σ j, collarModel n)) ∈ s
            have he : stepGlue C n (Sum.inr (⟨i, y⟩ : Σ j, collarModel n)) =
                (⟨RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ), hmem⟩ :
                  {x : X // x ∈ stepCollar C n}) := Subtype.ext rfl
            rw [he]
            exact hys
          · intro hx
            show RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) ∈ Ψ
            exact ⟨collarPiece_subset_stepCollar i ⟨(y : Fin (n + 1) → ℝ), y.2, rfl⟩, hx⟩
        obtain ⟨Fb, hFbc, hFb⟩ := isClosed_induced_iff.mp h1
        exact ⟨Fb, hFbc, fun y hy => by
          simpa using Set.ext_iff.mp hFb (⟨y, hy⟩ : collarModel n)⟩
      obtain ⟨G, hG, hGY⟩ :=
        exists_isClosed_stepCollar_inter (C := C) (n := n) (fun x hx => hx.1) hA hB
      exact isClosed_induced_iff.mpr ⟨G, hG, by
        ext x
        constructor
        · intro hx
          have hx' : (x : X) ∈ Ψ := by
            have h : (x : X) ∈ G ∩ stepCollar C n := ⟨hx, x.2⟩
            rwa [hGY] at h
          obtain ⟨h, hh⟩ := hx'
          rwa [show (⟨(x : X), h⟩ : {x : X // x ∈ stepCollar C n}) = x from
            Subtype.ext rfl] at hh
        · intro hx
          have hx' : (x : X) ∈ Ψ := ⟨x.2, hx⟩
          have h : (x : X) ∈ G ∩ stepCollar C n := by rw [hGY]; exact hx'
          exact h.1⟩
    · intro hs'
      exact hs'.preimage (continuous_stepGlue_aux C n)
  · rintro ⟨x, hx⟩
    rcases mem_stepCollar.mp hx with h | ⟨i, h⟩
    · exact ⟨Sum.inl ⟨x, h⟩, Subtype.ext rfl⟩
    · obtain ⟨y, hy, rfl⟩ := h
      exact ⟨Sum.inr ⟨i, ⟨y, hy⟩⟩, Subtype.ext rfl⟩

end Work.CWTOP
