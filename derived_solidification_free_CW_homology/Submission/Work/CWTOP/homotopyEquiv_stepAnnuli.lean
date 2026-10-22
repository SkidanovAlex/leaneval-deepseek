/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.isClosed_skeleton_diff_openCell

/-!
# The annuli of the `(n+1)`-skeleton are disjoint unions of model spheres

For a Hausdorff CW complex `C ⊆ X` and `n : ℕ`, we prove that the space

`{x : X // x ∈ stepCollar C n ∩ stepV C n}`

— the collar of the `(n+1)`-skeleton intersected with the union of the open `(n+1)`-cells — is
homotopy equivalent to the disjoint union `Σ j : cell C (n+1), modelSphere n`, one model sphere for
each top cell.

## The argument

Write `N = n + 1`.  The collar space is `stepCollar C n = skel C n ∪ ⋃ j, map j '' modelCollar n`,
where `modelCollar n = {1/2 < ‖y‖ ≤ 1}`, and the open top cells are `stepV C n = ⋃ j, openCell N j`.

1. **The pieces.**  As the open cells are disjoint from the `n`-skeleton,
   `stepAnnulus = stepCollar ∩ stepV` is the disjoint union of the pieces
   `annulusPiece n j = map j '' stepShell n`, where
   `stepShell n = {1/2 < ‖y‖ < 1}` is the open shell of the `j`-th model disk
   (`mem_annulusPiece_iff_mem_openCell`).  Each piece is the trace on `stepAnnulus` of the *open*
   cell `openCell N j` (`annulusPiece_eq_openCell_pieceZ`), which is open in the skeleton by
   `isClosed_skeleton_diff_openCell`; hence the cell of a point is locally constant
   (`continuous_toShellSigmaFun`) and `stepAnnulus` is homeomorphic to the disjoint union
   `Σ j, {y // y ∈ stepShell n}` of the model shells (`homeoStepAnnulus`).
2. **The model shell is a sphere.**  `{1/2 < ‖y‖ < 1} ≃ Sⁿ` by radial projection and scaling,
   i.e. `homotopyEquiv_stepShell_modelSphere`.
3. A disjoint union of homotopy equivalences with constant fibre is a homotopy equivalence
   (`homotopyEquivSigmaConst`).

## Main result

* `Work.CWTOP.homotopyEquiv_stepAnnuli`
-/

open CategoryTheory Limits Topology Set Function Metric
open scoped ContinuousMap

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## §0 Disjoint unions of a homotopy equivalence

A homotopy equivalence `e : A ≃ₕ B` lifts to the disjoint unions `Σ i, A → Σ i, B`, by applying it
on every summand.  The homotopies are lifted the same way; continuity is checked summandwise. -/

lemma continuous_sigma_of_isOpen_fibers {Z : Type*} [TopologicalSpace Z] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f : Z → Σ i, Y i}
    (hopen : ∀ i, IsOpen {z | (f z).1 = i})
    (hcont : ∀ i, ContinuousOn f {z | (f z).1 = i}) : Continuous f :=
  continuous_of_cover_nhds (s := fun i => {z | (f z).1 = i})
    (fun z => ⟨(f z).1, (hopen _).mem_nhds rfl⟩) hcont

/-- A continuous map `A → B` induces a continuous map of the disjoint unions with a fixed fibre. -/
def sigmaMapConst {ι : Type*} {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) : C((Σ _ : ι, A), (Σ _ : ι, B)) :=
  ⟨Sigma.map id (fun _ => f), Continuous.sigma_map (fun _ => f.continuous)⟩

@[simp] lemma sigmaMapConst_apply {ι : Type*} {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (f : C(A, B)) (p : Σ _ : ι, A) :
    sigmaMapConst (ι := ι) f p = ⟨p.1, f p.2⟩ := rfl

lemma sigmaMapConst_comp {ι : Type*} {A B D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace D] (f : C(B, D)) (g : C(A, B)) :
    (sigmaMapConst (ι := ι) f).comp (sigmaMapConst (ι := ι) g)
      = sigmaMapConst (ι := ι) (f.comp g) := by
  ext p <;> simp

lemma sigmaMapConst_id {ι : Type*} {A : Type*} [TopologicalSpace A] :
    sigmaMapConst (ι := ι) (ContinuousMap.id A) = ContinuousMap.id (Σ _ : ι, A) := by
  ext p <;> simp

/-- A homotopy between maps `A → B` induces a homotopy between the induced maps of the disjoint
unions with a fixed fibre. -/
def homotopySigmaConst {ι : Type*} {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f₀ f₁ : C(A, B)} (H : ContinuousMap.Homotopy f₀ f₁) :
    ContinuousMap.Homotopy (sigmaMapConst (ι := ι) f₀) (sigmaMapConst (ι := ι) f₁) where
  toContinuousMap :=
    ⟨fun p : unitInterval × (Σ _ : ι, A) => ⟨p.2.1, (H (p.1, p.2.2))⟩, by
      refine continuous_sigma_of_isOpen_fibers ?_ ?_
      · intro i
        have h : Continuous fun p : unitInterval × (Σ _ : ι, A) => (p.2 : Σ _ : ι, A) :=
          continuous_snd
        have := (isOpen_range_sigmaMk (i := i)).preimage h
        convert this using 2
        ext p
        simp
      · intro i
        have hsnd : Continuous fun q : (Σ _ : ι, A) => (q.2 : A) :=
          continuous_sigma_iff.mpr (fun i => continuous_id)
        have hbase : Continuous fun p : unitInterval × (Σ _ : ι, A) =>
            (⟨i, H (p.1, p.2.2)⟩ : Σ _ : ι, B) :=
          continuous_sigmaMk.comp (H.continuous.comp
            (continuous_fst.prodMk (hsnd.comp continuous_snd)))
        refine hbase.continuousOn.congr ?_
        intro p hp
        have hp' : p.2.1 = i := hp
        show (⟨p.2.1, H (p.1, p.2.2)⟩ : Σ _ : ι, B) = ⟨i, H (p.1, p.2.2)⟩
        rw [hp']⟩
  map_zero_left := by intro x; simp
  map_one_left := by intro x; simp

/-- A homotopy equivalence `A ≃ₕ B` induces a homotopy equivalence of the disjoint unions
`Σ _ : ι, A ≃ₕ Σ _ : ι, B` with an arbitrary index type. -/
noncomputable def homotopyEquivSigmaConst {ι : Type*} {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₕ B) : (Σ _ : ι, A) ≃ₕ (Σ _ : ι, B) :=
  ⟨sigmaMapConst (ι := ι) e.toFun, sigmaMapConst (ι := ι) e.invFun, by
      have h := Nonempty.map (homotopySigmaConst (ι := ι)) e.left_inv
      rw [← sigmaMapConst_comp, sigmaMapConst_id] at h
      exact h,
    by
      have h := Nonempty.map (homotopySigmaConst (ι := ι)) e.right_inv
      rw [← sigmaMapConst_comp, sigmaMapConst_id] at h
      exact h⟩

/-! ## §1 The model shell -/

/-- The open model shell `1/2 < ‖y‖ < 1` inside the model disk. -/
abbrev stepShell (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | (1 / 2 : ℝ) < ‖y‖ ∧ ‖y‖ < 1}

lemma mem_stepShell {n : ℕ} {y : Fin (n + 1) → ℝ} :
    y ∈ stepShell n ↔ (1 / 2 : ℝ) < ‖y‖ ∧ ‖y‖ < 1 := Iff.rfl

lemma stepShell_norm_pos {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ stepShell n) : 0 < ‖y‖ :=
  lt_trans (by norm_num) hy.1

lemma stepShell_ne_zero {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ stepShell n) : y ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (stepShell_norm_pos hy))

lemma stepShell_subset_ball {n : ℕ} :
    stepShell n ⊆ Metric.ball (0 : Fin (n + 1) → ℝ) 1 := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  exact hy.2

lemma stepShell_subset_closedBall {n : ℕ} :
    stepShell n ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
  fun y hy => Metric.ball_subset_closedBall (stepShell_subset_ball hy)

lemma stepShell_subset_modelCollar {n : ℕ} : stepShell n ⊆ modelCollar n :=
  fun _ hy => ⟨hy.1, le_of_lt hy.2⟩

lemma modelCollar_subset_closedBall' {n : ℕ} :
    modelCollar n ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hy.2

/-! ## §2 The annulus space and its pieces -/

/-- The collar space of the `(n+1)`-skeleton cut down to the union of the open top cells. -/
abbrev stepAnnulus (n : ℕ) : Set X := stepCollar C n ∩ stepV C n

lemma stepAnnulus_subset_skel {n : ℕ} : stepAnnulus (C := C) n ⊆ skel C (n + 1) := by
  rintro x ⟨hCollar, -⟩
  rw [stepCollar, mem_union] at hCollar
  rcases hCollar with hS | hcoll
  · exact skel_subset_skel_succ hS
  · rw [mem_iUnion] at hcoll
    obtain ⟨j, y, hy, rfl⟩ := hcoll
    exact RelCWComplex.closedCell_subset_skeleton (n + 1) j
      ⟨y, modelCollar_subset_closedBall' hy, rfl⟩

/-- The piece of the annulus space belonging to the cell `j`: interior of the collar of the
`j`-th `(n+1)`-cell, i.e. the image of the open shell in the coordinates of that cell. -/
def annulusPiece (n : ℕ) (j : RelCWComplex.cell C (n + 1)) : Set X :=
  RelCWComplex.map (n + 1) j '' stepShell n

lemma annulusPiece_subset_stepAnnulus (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    annulusPiece (C := C) n j ⊆ stepAnnulus (C := C) n := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨Or.inr (mem_iUnion.mpr ⟨j, y, stepShell_subset_modelCollar hy, rfl⟩),
    mem_iUnion.mpr ⟨j, y, stepShell_subset_ball hy, rfl⟩⟩

/-! ## §3 The coordinates of a piece -/

lemma stepCollar_cellCoord_map (n : ℕ) (j : RelCWComplex.cell C n) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball 0 1) : cellCoord C n j (RelCWComplex.map n j y) = y :=
  PartialEquiv.left_inv _ (by rwa [RelCWComplex.source_eq])

/-- **The pieces of the annulus space.**  A point of `stepCollar ∩ stepV` lies in the piece of
exactly those cells whose open cell contains it. -/
lemma mem_annulusPiece_iff_mem_openCell {n : ℕ} (j : RelCWComplex.cell C (n + 1)) {x : X}
    (hx : x ∈ stepAnnulus (C := C) n) :
    x ∈ annulusPiece (C := C) n j ↔ x ∈ RelCWComplex.openCell (n + 1) j := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, stepShell_subset_ball hy, rfl⟩
  · intro hxoc
    obtain ⟨hCollar, -⟩ := hx
    obtain ⟨y, hyball, rfl⟩ := hxoc
    rw [stepCollar, mem_union] at hCollar
    rcases hCollar with hS | hcoll
    · exfalso
      exact (Set.disjoint_left.mp
        (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1)
          (j := j) (by exact_mod_cast Nat.lt_succ_self n))
        hS) ⟨y, hyball, rfl⟩
    · rw [mem_iUnion] at hcoll
      obtain ⟨i, z, hz, hzi⟩ := hcoll
      have hzlt : ‖z‖ < 1 := by
        rcases lt_or_eq_of_le hz.2 with h | h
        · exact h
        · exfalso
          have hfront : RelCWComplex.map (n + 1) i z ∈ skel C n :=
            RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := i)
              ⟨z, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h ▸ rfl, rfl⟩
          rw [hzi] at hfront
          exact (Set.disjoint_left.mp
            (RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1)
              (j := j) (by exact_mod_cast Nat.lt_succ_self n))
            hfront) ⟨y, hyball, rfl⟩
      have hzball : z ∈ Metric.ball (0 : Fin (n + 1) → ℝ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hzlt
      have heq : (⟨n + 1, i⟩ : Σ l, RelCWComplex.cell C l) = ⟨n + 1, j⟩ :=
        eq_of_openCell_mem (C := C) ⟨z, hzball, rfl⟩ ⟨y, hyball, hzi.symm⟩
      have hij : i = j := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      subst hij
      exact ⟨z, ⟨hz.1, hzlt⟩, hzi⟩

lemma exists_mem_annulusPiece {n : ℕ} {x : X} (hx : x ∈ stepAnnulus (C := C) n) :
    ∃ j : RelCWComplex.cell C (n + 1), x ∈ annulusPiece (C := C) n j := by
  have hV : x ∈ stepV C n := hx.2
  rw [stepV, mem_iUnion] at hV
  obtain ⟨j, hj⟩ := hV
  exact ⟨j, (mem_annulusPiece_iff_mem_openCell (C := C) j hx).mpr hj⟩

lemma eq_cell_of_mem_annulusPiece {n : ℕ} {i j : RelCWComplex.cell C (n + 1)} {x : X}
    (hi : x ∈ annulusPiece (C := C) n i) (hj : x ∈ annulusPiece (C := C) n j) : i = j := by
  obtain ⟨y, hy, hyx⟩ := hi
  obtain ⟨y', hy', hyx'⟩ := hj
  have h1 : x ∈ RelCWComplex.openCell (n + 1) i := ⟨y, stepShell_subset_ball hy, hyx⟩
  have h2 : x ∈ RelCWComplex.openCell (n + 1) j := ⟨y', stepShell_subset_ball hy', hyx'⟩
  have := eq_of_openCell_mem (C := C) h1 h2
  exact eq_of_heq (Sigma.mk.inj_iff.mp this).2

lemma cellCoord_mem_stepShell_of_mem_annulusPiece {n : ℕ} {j : RelCWComplex.cell C (n + 1)}
    {x : X} (hx : x ∈ annulusPiece (C := C) n j) :
    cellCoord C (n + 1) j x ∈ stepShell n := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [stepCollar_cellCoord_map (C := C) (n + 1) j (stepShell_subset_ball hy)]
  exact hy

/-! ## §4 The cell of a point is locally constant -/

/-- The set of points of the annulus space lying in the open cell `j`. -/
def pieceZ (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    Set {x : X // x ∈ stepAnnulus (C := C) n} :=
  {x | (x : X) ∈ RelCWComplex.openCell (n + 1) j}

/-- The piece `annulusPiece n j` is the trace of the open cell `j` on the annulus space. -/
lemma annulusPiece_eq_openCell_pieceZ (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    {x : {x : X // x ∈ stepAnnulus (C := C) n} | (x : X) ∈ annulusPiece (C := C) n j}
      = pieceZ (C := C) n j := by
  ext x
  exact mem_annulusPiece_iff_mem_openCell (C := C) j x.2

/-- The trace of an open cell on the annulus space is open: removing a top-dimensional open cell
from the `(n+1)`-skeleton leaves a closed set, and the annulus space lies in that skeleton. -/
lemma isOpen_pieceZ (n : ℕ) (j : RelCWComplex.cell C (n + 1)) :
    IsOpen (pieceZ (C := C) n j) := by
  have hset : pieceZ (C := C) n j
      = Subtype.val ⁻¹'
          ((((RelCWComplex.skeleton C (n + 1) : Set X) \
            RelCWComplex.openCell (n + 1) j))ᶜ) := by
    ext x
    rw [mem_preimage, mem_compl_iff, mem_sdiff]
    constructor
    · intro hx
      rintro ⟨-, hnot⟩
      exact hnot hx
    · intro hx
      by_contra hB
      exact hx ⟨stepAnnulus_subset_skel x.2, hB⟩
  rw [hset]
  exact ((isClosed_skeleton_diff_openCell (C := C) (n + 1) j).isOpen_compl).preimage
    continuous_subtype_val

/-! ## §5 The homeomorphism with the disjoint union of the model shells -/

/-- The index of the cell of a point of the annulus space. -/
def shellCell (n : ℕ) (x : {x : X // x ∈ stepAnnulus (C := C) n}) :
    RelCWComplex.cell C (n + 1) :=
  Classical.choose (exists_mem_annulusPiece (C := C) x.2)

lemma shellCell_spec (n : ℕ) (x : {x : X // x ∈ stepAnnulus (C := C) n}) :
    (x : X) ∈ annulusPiece (C := C) n (shellCell (C := C) n x) :=
  Classical.choose_spec (exists_mem_annulusPiece (C := C) x.2)

/-- The forward map: a point of the annulus space, its cell and its coordinate in that cell. -/
def toShellSigmaFun (n : ℕ) (x : {x : X // x ∈ stepAnnulus (C := C) n}) :
    (Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :=
  ⟨shellCell (C := C) n x,
    ⟨cellCoord C (n + 1) (shellCell (C := C) n x) (x : X),
      cellCoord_mem_stepShell_of_mem_annulusPiece (shellCell_spec (C := C) n x)⟩⟩

lemma toShellSigmaFun_eq_mk (n : ℕ) (x : {x : X // x ∈ stepAnnulus (C := C) n})
    (j : RelCWComplex.cell C (n + 1)) (hx : (x : X) ∈ annulusPiece (C := C) n j) :
    toShellSigmaFun (C := C) n x =
      ⟨j, ⟨cellCoord C (n + 1) j (x : X), cellCoord_mem_stepShell_of_mem_annulusPiece hx⟩⟩ := by
  have hcell : shellCell (C := C) n x = j :=
    eq_cell_of_mem_annulusPiece (shellCell_spec (C := C) n x) hx
  subst hcell
  rfl

/-- The inverse map: a cell and a coordinate in the model shell determine a point of the annulus
space. -/
def ofShellSigmaFun (n : ℕ)
    (p : Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :
    {x : X // x ∈ stepAnnulus (C := C) n} :=
  ⟨RelCWComplex.map (n + 1) p.1 (p.2 : Fin (n + 1) → ℝ),
    ⟨Or.inr (mem_iUnion.mpr ⟨p.1, (p.2 : Fin (n + 1) → ℝ),
        stepShell_subset_modelCollar p.2.2, rfl⟩),
      mem_iUnion.mpr ⟨p.1, (p.2 : Fin (n + 1) → ℝ), stepShell_subset_ball p.2.2, rfl⟩⟩⟩

lemma ofShellSigmaFun_toShellSigmaFun (n : ℕ) (x : {x : X // x ∈ stepAnnulus (C := C) n}) :
    ofShellSigmaFun (C := C) n (toShellSigmaFun (C := C) n x) = x := by
  refine Subtype.ext ?_
  exact map_cellCoord (C := C) (n := n + 1) (j := shellCell (C := C) n x)
    ((mem_annulusPiece_iff_mem_openCell (C := C) (shellCell (C := C) n x) x.2).mp
      (shellCell_spec (C := C) n x))

lemma toShellSigmaFun_ofShellSigmaFun (n : ℕ)
    (p : Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :
    toShellSigmaFun (C := C) n (ofShellSigmaFun (C := C) n p) = p := by
  obtain ⟨j, y, hy⟩ := p
  have hmem : (ofShellSigmaFun (C := C) n ⟨j, ⟨y, hy⟩⟩ : X) ∈ annulusPiece (C := C) n j :=
    ⟨y, hy, rfl⟩
  rw [toShellSigmaFun_eq_mk (C := C) n (ofShellSigmaFun (C := C) n ⟨j, ⟨y, hy⟩⟩) j hmem]
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Subtype.ext ?_
  exact stepCollar_cellCoord_map (C := C) (n + 1) j (stepShell_subset_ball hy)

/-! ## §6 Continuity -/

lemma continuous_cellCoord_of_openCell (n : ℕ) (j : RelCWComplex.cell C n) :
    Continuous fun x : RelCWComplex.openCell n j => cellCoord C n j (x : X) :=
  continuousOn_iff_continuous_restrict.mp
    ((RelCWComplex.continuousOn_symm n j).mono (openCell_subset_target n j))

/-- The cell of a point of the annulus space depends continuously on the point; equivalently, the
map which sends a point to its cell and its coordinate is continuous. -/
lemma continuous_toShellSigmaFun (n : ℕ) : Continuous (toShellSigmaFun (C := C) n) := by
  refine continuous_of_cover_nhds
    (s := fun j : RelCWComplex.cell C (n + 1) => pieceZ (C := C) n j) ?_ ?_
  · intro x
    obtain ⟨j, hj⟩ := exists_mem_annulusPiece (C := C) x.2
    exact ⟨j, (isOpen_pieceZ (C := C) n j).mem_nhds
      ((annulusPiece_eq_openCell_pieceZ (C := C) n j) ▸ hj)⟩
  · intro j
    rw [continuousOn_iff_continuous_restrict]
    let F : pieceZ (C := C) n j →
        (Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :=
      fun x => ⟨j, ⟨cellCoord C (n + 1) j ((x : {x : X // x ∈ stepAnnulus (C := C) n}) : X),
        cellCoord_mem_stepShell_of_mem_annulusPiece
          ((mem_annulusPiece_iff_mem_openCell (C := C) j
            (x : {x : X // x ∈ stepAnnulus (C := C) n}).2).mpr x.2)⟩⟩
    have hval : Continuous fun x : pieceZ (C := C) n j =>
        (⟨((x : {x : X // x ∈ stepAnnulus (C := C) n}) : X), x.2⟩ :
          RelCWComplex.openCell (n + 1) j) :=
      Continuous.subtype_mk (f := fun x : pieceZ (C := C) n j =>
        ((x : {x : X // x ∈ stepAnnulus (C := C) n}) : X))
        (continuous_subtype_val.comp continuous_subtype_val) _
    have hcoord : Continuous fun x : pieceZ (C := C) n j =>
        cellCoord C (n + 1) j ((x : {x : X // x ∈ stepAnnulus (C := C) n}) : X) :=
      (continuous_cellCoord_of_openCell (C := C) (n + 1) j).comp hval
    have hF : Continuous F :=
      continuous_sigmaMk.comp (Continuous.subtype_mk hcoord _)
    refine Continuous.congr hF ?_
    intro x
    rw [Set.domRestrict_apply]
    exact (toShellSigmaFun_eq_mk (C := C) n
      (x : {x : X // x ∈ stepAnnulus (C := C) n}) j
      ((mem_annulusPiece_iff_mem_openCell (C := C) j
        (x : {x : X // x ∈ stepAnnulus (C := C) n}).2).mpr x.2)).symm

lemma continuous_ofShellSigmaFun (n : ℕ) : Continuous (ofShellSigmaFun (C := C) n) := by
  refine Continuous.subtype_mk (f := fun p :
      (Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) =>
      RelCWComplex.map (n + 1) p.1 (p.2 : Fin (n + 1) → ℝ)) ?_
    (fun p => ⟨Or.inr (mem_iUnion.mpr ⟨p.1, (p.2 : Fin (n + 1) → ℝ),
        stepShell_subset_modelCollar p.2.2, rfl⟩),
      mem_iUnion.mpr ⟨p.1, (p.2 : Fin (n + 1) → ℝ), stepShell_subset_ball p.2.2, rfl⟩⟩)
  rw [continuous_sigma_iff]
  intro j
  exact continuousOn_iff_continuous_restrict.mp
    ((RelCWComplex.continuousOn (n + 1) j).mono
      (fun y hy => stepShell_subset_closedBall hy))

/-- The annulus space is the disjoint union of the model shells, one for each top cell. -/
def homeoStepAnnulus (n : ℕ) :
    {x : X // x ∈ stepAnnulus (C := C) n} ≃ₜ
      (Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) where
  toFun := toShellSigmaFun (C := C) n
  invFun := ofShellSigmaFun (C := C) n
  left_inv := ofShellSigmaFun_toShellSigmaFun (C := C) n
  right_inv := toShellSigmaFun_ofShellSigmaFun (C := C) n
  continuous_toFun := continuous_toShellSigmaFun (C := C) n
  continuous_invFun := continuous_ofShellSigmaFun (C := C) n

/-! ## §7 The model shell is homotopy equivalent to the model sphere -/

/-- The radial projection is invariant under positive scalings. -/
lemma radialUnit_smul_of_pos' {k : ℕ} {y : Fin k → ℝ} {r : ℝ} (hr : 0 < r) :
    radialUnit (r • y) = radialUnit y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [radialUnit]
  · have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    rw [radialUnit, radialUnit, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
    congr 1
    field_simp

/-- The radial deformation of the model shell towards the sphere of radius `3/4` stays inside the
shell: the norm of the deformed point is the convex combination `(1 - t) * (3/4) + t * ‖y‖` of two
numbers in `(1/2, 1)`. -/
lemma stepShell_smul_coeff_mem {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ stepShell n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) * (3 / 4) * ‖y‖⁻¹ + t) • y ∈ stepShell n := by
  have hypos : 0 < ‖y‖ := stepShell_norm_pos hy
  have hne : ‖y‖ ≠ 0 := ne_of_gt hypos
  have hc : 0 ≤ (1 - t) * (3 / 4) * ‖y‖⁻¹ + t := by
    have h1 : (0 : ℝ) ≤ 1 - t := by linarith
    have h3 : (0 : ℝ) ≤ ‖y‖⁻¹ := inv_nonneg.mpr (le_of_lt hypos)
    nlinarith [mul_nonneg (mul_nonneg h1 (by norm_num : (0 : ℝ) ≤ 3 / 4)) h3]
  have hnorm : ‖((1 - t) * (3 / 4) * ‖y‖⁻¹ + t) • y‖ = (1 - t) * (3 / 4) + t * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  rw [mem_stepShell]
  constructor <;> rw [hnorm] <;> nlinarith [hy.1, hy.2]

/-- A point of the model sphere has norm one. -/
lemma norm_eq_one_of_mem_modelSphere {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ modelSphere n) :
    ‖y‖ = 1 := by
  rw [modelSphere, Metric.mem_sphere, dist_eq_norm, sub_zero] at hy
  exact hy

/-- The radial projection from the model shell to the unit sphere. -/
def stepShellToSphereFun (n : ℕ) (y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) : modelSphere n :=
  ⟨radialUnit (y : Fin (n + 1) → ℝ), by
    rw [modelSphere]
    exact radialUnit_mem_sphere (stepShell_ne_zero y.2)⟩

/-- The scaling by `3/4` of the unit sphere, landing in the model shell. -/
def stepSphereToShellFun (n : ℕ) (y : modelSphere n) : {y : Fin (n + 1) → ℝ // y ∈ stepShell n} :=
  ⟨(3 / 4 : ℝ) • (y : Fin (n + 1) → ℝ), by
    rw [mem_stepShell, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4), norm_eq_one_of_mem_modelSphere y.2, mul_one]
    exact ⟨by norm_num, by norm_num⟩⟩

@[simp] lemma stepShellToSphereFun_apply (n : ℕ) (y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :
    ((stepShellToSphereFun n y : modelSphere n) : Fin (n + 1) → ℝ)
      = radialUnit (y : Fin (n + 1) → ℝ) := rfl

@[simp] lemma stepSphereToShellFun_apply (n : ℕ) (y : modelSphere n) :
    ((stepSphereToShellFun n y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) : Fin (n + 1) → ℝ)
      = (3 / 4 : ℝ) • (y : Fin (n + 1) → ℝ) := rfl

lemma continuous_stepShellToSphereFun (n : ℕ) : Continuous (stepShellToSphereFun n) := by
  refine Continuous.subtype_mk
    (f := fun y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      radialUnit (y : Fin (n + 1) → ℝ)) ?_ _
  have h1 : Continuous fun y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (‖(y : Fin (n + 1) → ℝ)‖)⁻¹ :=
    Continuous.inv₀ (continuous_norm.comp continuous_subtype_val)
      (fun y => ne_of_gt (stepShell_norm_pos y.2))
  have h2 : Continuous fun y : {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (y : Fin (n + 1) → ℝ) := continuous_subtype_val
  unfold radialUnit
  exact h1.smul h2

lemma continuous_stepSphereToShellFun (n : ℕ) : Continuous (stepSphereToShellFun n) := by
  refine Continuous.subtype_mk
    (f := fun y : modelSphere n => (3 / 4 : ℝ) • (y : Fin (n + 1) → ℝ)) ?_ _
  exact (continuous_const : Continuous fun _ : modelSphere n => (3 / 4 : ℝ)).smul
    continuous_subtype_val

/-- The radial projection, as a continuous map. -/
def stepShellToSphere (n : ℕ) : C({y : Fin (n + 1) → ℝ // y ∈ stepShell n}, modelSphere n) :=
  ⟨stepShellToSphereFun n, continuous_stepShellToSphereFun n⟩

/-- The scaling by `3/4`, as a continuous map into the shell. -/
def stepSphereToShell (n : ℕ) : C(modelSphere n, {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :=
  ⟨stepSphereToShellFun n, continuous_stepSphereToShellFun n⟩

/-- The radial deformation of the model shell. -/
def stepShellDeformationFun (n : ℕ)
    (p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :
    {y : Fin (n + 1) → ℝ // y ∈ stepShell n} :=
  ⟨((1 - (p.1 : ℝ)) * (3 / 4) * ‖(p.2 : Fin (n + 1) → ℝ)‖⁻¹ + (p.1 : ℝ)) •
      (p.2 : Fin (n + 1) → ℝ),
    stepShell_smul_coeff_mem p.2.2 p.1.2.1 p.1.2.2⟩

@[simp] lemma stepShellDeformationFun_apply (n : ℕ)
    (p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :
    ((stepShellDeformationFun n p : {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) : Fin (n + 1) → ℝ)
      = ((1 - (p.1 : ℝ)) * (3 / 4) * ‖(p.2 : Fin (n + 1) → ℝ)‖⁻¹ + (p.1 : ℝ)) •
          (p.2 : Fin (n + 1) → ℝ) := rfl

lemma continuous_stepShellDeformationFun (n : ℕ) : Continuous (stepShellDeformationFun n) := by
  refine Continuous.subtype_mk
    (f := fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      ((1 - (p.1 : ℝ)) * (3 / 4) * ‖(p.2 : Fin (n + 1) → ℝ)‖⁻¹ + (p.1 : ℝ)) •
        (p.2 : Fin (n + 1) → ℝ))
    ?_ (fun p => stepShell_smul_coeff_mem p.2.2 p.1.2.1 p.1.2.2)
  have ht : Continuous fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (p.2 : Fin (n + 1) → ℝ) := continuous_subtype_val.comp continuous_snd
  have hnorm : Continuous fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      ‖(p.2 : Fin (n + 1) → ℝ)‖ := continuous_norm.comp hy
  have hinv : Continuous fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (‖(p.2 : Fin (n + 1) → ℝ)‖)⁻¹ :=
    hnorm.inv₀ (fun p => ne_of_gt (stepShell_norm_pos p.2.2))
  have hcoef : Continuous fun p : unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n} =>
      (1 - (p.1 : ℝ)) * (3 / 4) * ‖(p.2 : Fin (n + 1) → ℝ)‖⁻¹ + (p.1 : ℝ) :=
    (((continuous_const.sub ht).mul continuous_const).mul hinv).add ht
  exact hcoef.smul hy

/-- The radial deformation, as a continuous map. -/
def stepShellDeformation (n : ℕ) :
    C(unitInterval × {y : Fin (n + 1) → ℝ // y ∈ stepShell n},
      {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) :=
  ⟨stepShellDeformationFun n, continuous_stepShellDeformationFun n⟩

/-- `stepSphereToShell ∘ stepShellToSphere` is homotopic to the identity of the model shell. -/
def stepShellHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((stepSphereToShell n).comp (stepShellToSphere n))
      (ContinuousMap.id {y : Fin (n + 1) → ℝ // y ∈ stepShell n}) where
  toContinuousMap := stepShellDeformation n
  map_zero_left y := by
    change stepShellDeformationFun n (0, y) = stepSphereToShellFun n (stepShellToSphereFun n y)
    apply Subtype.ext
    simp only [stepShellDeformationFun_apply, stepSphereToShellFun_apply, stepShellToSphereFun_apply,
      Set.Icc.coe_zero, sub_zero, one_mul, add_zero, radialUnit, smul_smul]
  map_one_left y := by
    change stepShellDeformationFun n (1, y) = y
    apply Subtype.ext
    simp only [stepShellDeformationFun_apply, Set.Icc.coe_one, sub_self, zero_mul, zero_add,
      one_smul]

/-- `stepShellToSphere ∘ stepSphereToShell` is the identity of the model sphere. -/
theorem stepShellToSphere_comp_stepSphereToShell (n : ℕ) :
    (stepShellToSphere n).comp (stepSphereToShell n) = ContinuousMap.id (modelSphere n) := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  show radialUnit ((3 / 4 : ℝ) • (y : Fin (n + 1) → ℝ)) = (y : Fin (n + 1) → ℝ)
  rw [radialUnit_smul_of_pos' (by norm_num : (0 : ℝ) < 3 / 4)]
  exact radialUnit_eq_self_of_norm_eq_one (norm_eq_one_of_mem_modelSphere y.2)

/-- **The model shell is homotopy equivalent to the model sphere.**  The maps are the radial
projection `y ↦ radialUnit y` and the scaling `y ↦ (3/4) • y`, which is a homotopy inverse because
the radial deformation `y ↦ ((1 - t) * (3/4) * ‖y‖⁻¹ + t) • y` joins the composite
`y ↦ (3/4) • radialUnit y` to the identity inside the shell. -/
theorem homotopyEquiv_stepShell_modelSphere (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (TopCat.of {y : Fin (n + 1) → ℝ // y ∈ stepShell n})
      (TopCat.of (Work.CWTOP.modelSphere n))) :=
  ⟨{ toFun := stepShellToSphere n
     invFun := stepSphereToShell n
     left_inv := ⟨stepShellHomotopy n⟩
     right_inv := by rw [stepShellToSphere_comp_stepSphereToShell n] }⟩

/-! ## §8 The theorem -/

theorem homotopyEquiv_stepAnnuli {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (TopCat.of {x : X // x ∈ Work.CWTOP.stepCollar C n ∩ Work.CWTOP.stepV C n})
      (TopCat.of (Σ j : Topology.RelCWComplex.cell C (n + 1), Work.CWTOP.modelSphere n))) := by
  obtain ⟨e⟩ := homotopyEquiv_stepShell_modelSphere n
  exact ⟨(homeoStepAnnulus (C := C) n).toHomotopyEquiv.trans
    (homotopyEquivSigmaConst (ι := RelCWComplex.cell C (n + 1)) e)⟩

end Work.CWTOP
