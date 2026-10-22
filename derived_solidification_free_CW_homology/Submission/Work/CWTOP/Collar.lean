/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Work.CWTOP.Basic

/-!
# The collar pieces of the `(n+1)`-skeleton

Vocabulary and elementary geometry for the step maps of `Submission.Work.CWTOP.Basic`, used by
`Submission.Work.CWTOP.isQuotientMap_stepGlue`.

For a top cell `i` of a Hausdorff CW complex `C ⊆ X` we write

* `collarPiece C n i` for the image of the model collar `modelCollar n` under the characteristic
  map of `i` (this is the corresponding summand of `stepPieces`);
* `innerDiskCell C n i` for the image of the closed disk of radius `1/2`, so that the closed cell
  of `i` is the disjoint union of `collarPiece C n i` and `innerDiskCell C n i`, and
  `stepCollar C n ∩ closedCell (n+1) i = collarPiece C n i`;
* `collarMap C n i` for the parametrisation of the collar piece by the model collar.
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- The model collar of the `(n+1)`-cells, as a type. -/
abbrev collarModel (n : ℕ) : Type := {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}

/-- The collar piece of the `(n+1)`-cell `i`: the image of the model collar under the
characteristic map of `i`. -/
def collarPiece (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C (n + 1)) : Set X :=
  RelCWComplex.map (n + 1) i '' modelCollar n

/-- The inner closed disk of the `(n+1)`-cell `i`: the image of the closed disk of radius `1/2`. -/
def innerDiskCell (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C (n + 1)) : Set X :=
  RelCWComplex.map (n + 1) i '' Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2)

/-- The parametrisation of the collar piece of `i` by the model collar. -/
def collarMap (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C (n + 1)) :
    collarModel n → {x : X // x ∈ collarPiece C n i} :=
  fun y => ⟨RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ), y, y.2, rfl⟩

variable {n : ℕ}

@[simp]
lemma collarMap_coe (i : RelCWComplex.cell C (n + 1)) (y : collarModel n) :
    ((collarMap C n i y : {x : X // x ∈ collarPiece C n i}) : X)
      = RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) := rfl

lemma mem_collarPiece {i : RelCWComplex.cell C (n + 1)} {x : X} :
    x ∈ collarPiece C n i ↔ ∃ y ∈ modelCollar n, RelCWComplex.map (n + 1) i y = x := Iff.rfl

lemma mem_innerDiskCell {i : RelCWComplex.cell C (n + 1)} {x : X} :
    x ∈ innerDiskCell C n i ↔
      ∃ y ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2), RelCWComplex.map (n + 1) i y = x :=
  Iff.rfl

lemma collarModel_subset_closedBall :
    modelCollar n ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := fun _ hy => by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hy.2

lemma closedBall_half_subset_closedBall :
    Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2) ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
  Metric.closedBall_subset_closedBall (by norm_num)

lemma collarPiece_subset_closedCell (i : RelCWComplex.cell C (n + 1)) :
    collarPiece C n i ⊆ RelCWComplex.closedCell (n + 1) i :=
  image_mono collarModel_subset_closedBall

lemma innerDiskCell_subset_closedCell (i : RelCWComplex.cell C (n + 1)) :
    innerDiskCell C n i ⊆ RelCWComplex.closedCell (n + 1) i :=
  image_mono closedBall_half_subset_closedBall

lemma collarPiece_subset_skel_succ (i : RelCWComplex.cell C (n + 1)) :
    collarPiece C n i ⊆ skel C (n + 1) :=
  (collarPiece_subset_closedCell i).trans (RelCWComplex.closedCell_subset_skeleton _ _)

lemma innerDiskCell_subset_skel_succ (i : RelCWComplex.cell C (n + 1)) :
    innerDiskCell C n i ⊆ skel C (n + 1) :=
  (innerDiskCell_subset_closedCell i).trans (RelCWComplex.closedCell_subset_skeleton _ _)

lemma mem_stepCollar {x : X} :
    x ∈ stepCollar C n ↔
      x ∈ skel C n ∨ ∃ i : RelCWComplex.cell C (n + 1), x ∈ collarPiece C n i := by
  rw [stepCollar, mem_union, mem_iUnion]
  exact Iff.rfl

lemma collarPiece_subset_stepCollar (i : RelCWComplex.cell C (n + 1)) :
    collarPiece C n i ⊆ stepCollar C n :=
  fun _ hx => mem_stepCollar.mpr (Or.inr ⟨i, hx⟩)

lemma stepCollar_subset_skel_succ : stepCollar C n ⊆ skel C (n + 1) := by
  intro x hx
  rcases mem_stepCollar.mp hx with h | ⟨i, hi⟩
  · exact skel_subset_skel_succ h
  · exact collarPiece_subset_skel_succ i hi

lemma isCompact_innerDiskCell (i : RelCWComplex.cell C (n + 1)) :
    IsCompact (innerDiskCell C n i) := by
  have hc : Continuous fun y : {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 (1 / 2)} =>
      RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ) :=
    continuousOn_iff_continuous_restrict.mp
      ((RelCWComplex.continuousOn (n + 1) i).mono closedBall_half_subset_closedBall)
  haveI : CompactSpace {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 (1 / 2)} :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 (1 / 2))
  have hset : innerDiskCell C n i =
      (fun y : {y : Fin (n + 1) → ℝ // y ∈ Metric.closedBall 0 (1 / 2)} =>
        RelCWComplex.map (n + 1) i (y : Fin (n + 1) → ℝ)) '' Set.univ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
  rw [hset]
  exact isCompact_univ.image hc

lemma isClosed_innerDiskCell (i : RelCWComplex.cell C (n + 1)) :
    IsClosed (innerDiskCell C n i) :=
  (isCompact_innerDiskCell i).isClosed

lemma innerDiskCell_subset_openCell (i : RelCWComplex.cell C (n + 1)) :
    innerDiskCell C n i ⊆ RelCWComplex.openCell (n + 1) i := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  have h := Metric.mem_closedBall.mp hy
  rw [dist_zero_right] at h
  linarith

end Work.CWTOP
