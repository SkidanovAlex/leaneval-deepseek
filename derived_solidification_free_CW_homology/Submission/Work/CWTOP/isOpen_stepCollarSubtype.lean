/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.CWTOP.Closed
import Submission.Work.CWTOP.Pieces
import Submission.Work.CWTOP.Collar
import Submission.Work.CWTOP.isQuotientMap_stepGlue

/-!
# The collar space is open in the next skeleton

`stepCollar C n` is the `n`-skeleton together with the collars `1/2 < ‖y‖ ≤ 1` of the
`(n+1)`-cells. We prove that it is *open* in the `(n+1)`-skeleton, i.e. that

`{x : ↥(skel C (n+1)) | (x : X) ∈ stepCollar C n}`

is open. Equivalently, the complement of `stepCollar C n` inside `skel C (n+1)` is closed in `X`;
that complement is exactly the union of the inner closed disks `innerDiskCell C n i` of the
`(n+1)`-cells.

The proof is an application of the weak topology of a CW complex
(`CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`). For a cell of dimension
`m` we distinguish three cases:

* `m < n+1`: the whole open cell lies in the `n`-skeleton, hence in `stepCollar C n`, so it misses
  the complement;
* `m = n+1`: the intersection with the closed cell `closedCell (n+1) i` is
  `closedCell (n+1) i \ collarPiece C n i = innerDiskCell C n i`, which is compact (hence closed);
* `m > n+1`: the open cell misses `skel C (n+1)` altogether.

The two cell-geometry inputs `closedCell_inter_stepCollar` and `closedCell_sdiff_collarPiece` are
proved in `Submission.Work.CWTOP.isQuotientMap_stepGlue`.
-/

open Topology Set Function

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## §1 The complement inside a top closed cell -/

/-- Intersecting the complement of the collar space in the `(n+1)`-skeleton with a closed top cell
gives the inner closed disk of that cell. -/
lemma sdiff_stepCollar_inter_closedCell {n : ℕ} (i : RelCWComplex.cell C (n + 1)) :
    (skel C (n + 1) \ stepCollar C n) ∩ RelCWComplex.closedCell (n + 1) i
      = innerDiskCell C n i := by
  rw [← closedCell_sdiff_collarPiece (C := C) i]
  have hK : RelCWComplex.closedCell (n + 1) i ⊆ skel C (n + 1) :=
    RelCWComplex.closedCell_subset_skeleton (n + 1) i
  have hT : RelCWComplex.closedCell (n + 1) i ∩ stepCollar C n = collarPiece C n i :=
    closedCell_inter_stepCollar i
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨⟨-, hxT⟩, hxK⟩
    exact ⟨hxK, fun hc => hxT (collarPiece_subset_stepCollar i hc)⟩
  · rintro ⟨hxK, hc⟩
    refine ⟨⟨hK hxK, ?_⟩, hxK⟩
    intro hstep
    exact hc (by rw [← hT]; exact ⟨hxK, hstep⟩)

/-! ## §2 The complement is closed -/

/-- The complement of the collar space in the `(n+1)`-skeleton is closed in `X`. -/
theorem isClosed_skel_sdiff_stepCollar (n : ℕ) :
    IsClosed (skel C (n + 1) \ stepCollar C n) := by
  refine CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell (C := C)
    (A := skel C (n + 1) \ stepCollar C n) ?_ ?_
  · intro x hx
    exact skel_subset_complex_aux (C := C) (n + 1) hx.1
  · intro m _ j
    rcases lt_trichotomy m (n + 1) with hlt | heq | hgt
    · -- a lower dimensional cell lies in the `n`-skeleton, hence in the collar space
      left
      rw [Set.disjoint_left]
      intro x hx hxo
      exact hx.2 (skel_subset_stepCollar (C := C)
        (skel_mono_aux (C := C) (Nat.lt_succ_iff.mp hlt)
          (RelCWComplex.openCell_subset_skeleton m j hxo)))
    · -- the top cell itself contributes exactly its inner closed disk
      cases heq
      right
      rw [sdiff_stepCollar_inter_closedCell (C := C) (n := n) j]
      exact isClosed_innerDiskCell (C := C) j
    · -- a higher dimensional open cell misses the `(n+1)`-skeleton
      left
      rw [Set.disjoint_left]
      intro x hx hxo
      exact Set.disjoint_left.mp
        (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := ((n + 1 : ℕ) : ℕ∞))
          (m := m) (j := j) (by exact_mod_cast hgt)) hx.1 hxo

/-! ## §3 The collar space is open in the `(n+1)`-skeleton -/

theorem isOpen_stepCollarSubtype {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) :
    IsOpen {x : ↥(Work.CWTOP.skel C (n + 1)) | (x : X) ∈ Work.CWTOP.stepCollar C n} := by
  have hA := isClosed_skel_sdiff_stepCollar (C := C) n
  have hpre : IsClosed ((Subtype.val : ↥(skel C (n + 1)) → X) ⁻¹'
      (skel C (n + 1) \ stepCollar C n)) := hA.preimage continuous_subtype_val
  have heq : ({x : ↥(skel C (n + 1)) | (x : X) ∈ stepCollar C n})ᶜ
      = (Subtype.val : ↥(skel C (n + 1)) → X) ⁻¹' (skel C (n + 1) \ stepCollar C n) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff]
    constructor
    · intro h; exact ⟨x.2, h⟩
    · rintro ⟨-, h⟩; exact h
  rw [← isClosed_compl_iff, heq]
  exact hpre

end Work.CWTOP
