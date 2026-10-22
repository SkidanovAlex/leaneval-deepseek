/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Blueprint.Interfaces
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Maps.Proper.Basic

/-!
# CWTOP: the basic cell calculus for Hausdorff CW complexes

This file sets up the vocabulary used by the area `CWTOP`:

* `cellCentre`, `centres` : the centres of the cells of a given dimension;
* `cellCoord` : the coordinate of a point of an open cell in the model disk;
* `modelCollar`, `modelAnnulus`, `modelSphere` : the model pieces used in the induction step
  `Xₙ ↪ Xₙ₊₁`;
* `stepU`, `stepV` : the two open sets covering the `(n+1)`-skeleton;
* `stepPieces`, `stepGlue` : the "glued pieces" space `Xₙ ⊔ ⊔ collars` and its map to `Xₙ₊₁`;
* `stepRadialPiece`, `stepHomPiece` : the radial projection and the radial homotopy on the pieces.

The mathematical input for the induction step is that `stepGlue` is a quotient map and hence that
`stepRadialPiece` and `stepHomPiece` descend to maps on the `(n+1)`-skeleton; this is carried out
in `Submission.Work.CWTOP.Radial`.
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## §1 Centres of cells -/

/-- The centre of the cell `j`, i.e. the image of `0` under its characteristic map. -/
def cellCentre (C : Set X) [CWComplex C] (n : ℕ) (j : RelCWComplex.cell C n) : X :=
  RelCWComplex.map n j 0

/-- The set of centres of the `n`-cells. -/
def centres (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  ⋃ j : RelCWComplex.cell C n, {cellCentre C n j}

lemma mem_centres {n : ℕ} {x : X} :
    x ∈ centres C n ↔ ∃ j : RelCWComplex.cell C n, cellCentre C n j = x := by
  simp only [centres, mem_iUnion, mem_singleton_iff]
  exact ⟨fun ⟨j, h⟩ => ⟨j, h.symm⟩, fun ⟨j, h⟩ => ⟨j, h.symm⟩⟩

lemma cellCentre_mem_openCell (n : ℕ) (j : RelCWComplex.cell C n) :
    cellCentre C n j ∈ RelCWComplex.openCell n j :=
  RelCWComplex.map_zero_mem_openCell n j

lemma cellCentre_notMem_skeletonLT (n : ℕ) (j : RelCWComplex.cell C n) {m : ℕ} (h : m ≤ n) :
    cellCentre C n j ∉ (RelCWComplex.skeletonLT C m : Set X) := by
  have hd := RelCWComplex.disjoint_skeletonLT_openCell (C := C) (n := (m : ℕ∞)) (m := n) (j := j)
    (by exact_mod_cast h)
  exact fun hx => Set.disjoint_left.mp hd hx (cellCentre_mem_openCell n j)

lemma cellCentre_notMem_skeleton (n : ℕ) (j : RelCWComplex.cell C n) {m : ℕ} (h : m < n) :
    cellCentre C n j ∉ (RelCWComplex.skeleton C m : Set X) := by
  intro hx
  exact cellCentre_notMem_skeletonLT n j (m := m + 1) (by omega) hx

/-- The cell containing a point of an open cell is unique. -/
lemma eq_of_openCell_mem {n m : ℕ} {j : RelCWComplex.cell C n} {i : RelCWComplex.cell C m}
    {x : X} (hj : x ∈ RelCWComplex.openCell n j) (hi : x ∈ RelCWComplex.openCell m i) :
    (⟨n, j⟩ : Σ l, RelCWComplex.cell C l) = ⟨m, i⟩ := by
  by_contra hne
  exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := C) hne) hj hi

/-- A centre of an `n`-cell is not in the closed cell of any *other* cell of dimension `≤ n`. -/
lemma cellCentre_notMem_closedCell (n : ℕ) (j : RelCWComplex.cell C n) {m : ℕ}
    (i : RelCWComplex.cell C m) (hm : m ≤ n)
    (hne : (⟨m, i⟩ : Σ l, RelCWComplex.cell C l) ≠ ⟨n, j⟩) :
    cellCentre C n j ∉ RelCWComplex.closedCell m i := by
  intro hx
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
  rcases hx with hx | hx
  · exact cellCentre_notMem_skeletonLT n j hm
      (RelCWComplex.cellFrontier_subset_skeletonLT m i hx)
  · exact hne (eq_of_openCell_mem (C := C) hx (cellCentre_mem_openCell n j))

/-! ## §2 Coordinates in the model disk -/

/-- The coordinate of a point of the open cell `openCell C n j` in the model disk. -/
def cellCoord (C : Set X) [CWComplex C] (n : ℕ) (j : RelCWComplex.cell C n) (x : X) :
    Fin n → ℝ := (RelCWComplex.map n j).invFun x

lemma openCell_subset_target (n : ℕ) (j : RelCWComplex.cell C n) :
    RelCWComplex.openCell n j ⊆ (RelCWComplex.map n j).target := by
  rintro x ⟨y, hy, rfl⟩
  exact PartialEquiv.map_source _ (by rwa [RelCWComplex.source_eq])

lemma map_cellCoord {n : ℕ} {j : RelCWComplex.cell C n} {x : X}
    (hx : x ∈ RelCWComplex.openCell n j) :
    RelCWComplex.map n j (cellCoord C n j x) = x :=
  PartialEquiv.right_inv _ (openCell_subset_target n j hx)

lemma cellCoord_mem_ball {n : ℕ} {j : RelCWComplex.cell C n} {x : X}
    (hx : x ∈ RelCWComplex.openCell n j) : cellCoord C n j x ∈ Metric.ball 0 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : cellCoord C n j (RelCWComplex.map n j y) = y := by
    rw [cellCoord]
    exact PartialEquiv.left_inv _ (by rwa [RelCWComplex.source_eq])
  rw [h1]
  exact hy

/-- The unique cell containing a point of the `(n+1)`-skeleton that is not in the `n`-skeleton. -/
theorem exists_topCell {n : ℕ} {x : X} (hx : x ∈ (RelCWComplex.skeleton C (n + 1) : Set X))
    (hxS : x ∉ (RelCWComplex.skeleton C n : Set X)) :
    ∃ j : RelCWComplex.cell C (n + 1), x ∈ RelCWComplex.openCell (n + 1) j := by
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  obtain ⟨m, hm, j, hj⟩ := hx
  have hm' : m ≤ n + 1 := by exact_mod_cast hm
  rcases Nat.lt_or_ge m (n + 1) with hlt | hge
  · refine absurd (CWComplex.mem_skeleton_iff.mpr ⟨m, ?_, j, hj⟩) (by rwa [SetLike.mem_coe] at hxS)
    exact (Nat.cast_le (α := ℕ∞)).mpr (Nat.lt_succ_iff.mp hlt)
  · have hm_eq : m = n + 1 := le_antisymm hm' hge
    cases hm_eq
    exact ⟨j, hj⟩

/-! ## §3 Model pieces -/

/-- The model collar `1/2 < ‖y‖ ≤ 1` inside the model disk. -/
def modelCollar (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | (1 / 2 : ℝ) < ‖y‖ ∧ ‖y‖ ≤ 1}

/-- The model annulus `1/2 < ‖y‖ < 3/4` inside the model disk. -/
def modelAnnulus (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {y | (1 / 2 : ℝ) < ‖y‖ ∧ ‖y‖ < (3 / 4 : ℝ)}

/-- The model sphere (with respect to the norm used in the CW structure). -/
def modelSphere (n : ℕ) : Set (Fin (n + 1) → ℝ) := Metric.sphere (0 : Fin (n + 1) → ℝ) 1

/-- The radial projection of a vector to the model sphere. -/
def radialUnit {k : ℕ} (y : Fin k → ℝ) : Fin k → ℝ := ‖y‖⁻¹ • y

/-- A globally continuous version of the radial projection; it agrees with `radialUnit` as soon as
`1/2 ≤ ‖y‖`. -/
def radialUnitSafe {k : ℕ} (y : Fin k → ℝ) : Fin k → ℝ := (max ‖y‖ (1 / 2))⁻¹ • y

lemma norm_radialUnit {k : ℕ} {y : Fin k → ℝ} (hy : y ≠ 0) : ‖radialUnit y‖ = 1 := by
  have h : ‖y‖ ≠ 0 := by simpa [norm_eq_zero] using hy
  rw [radialUnit, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
    inv_mul_cancel₀ h]

lemma radialUnit_mem_sphere {k : ℕ} {y : Fin k → ℝ} (hy : y ≠ 0) :
    radialUnit y ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact norm_radialUnit hy

lemma radialUnit_eq_self_of_norm_eq_one {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ = 1) :
    radialUnit y = y := by
  rw [radialUnit, hy, inv_one, one_smul]

lemma radialUnitSafe_eq_radialUnit {k : ℕ} {y : Fin k → ℝ} (hy : (1 / 2 : ℝ) < ‖y‖) :
    radialUnitSafe y = radialUnit y := by
  rw [radialUnitSafe, radialUnit, max_eq_left (le_of_lt hy)]

lemma norm_max_norm_half_ne_zero {k : ℕ} (y : Fin k → ℝ) : max ‖y‖ (1 / 2 : ℝ) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))

lemma norm_radialUnitSafe_le_one {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ ≤ 1) :
    ‖radialUnitSafe y‖ ≤ 1 := by
  rw [radialUnitSafe, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) (le_max_right _ _)))]
  by_cases h : ‖y‖ ≤ (1 / 2 : ℝ)
  · rw [max_eq_right h]
    nlinarith [norm_nonneg y]
  · rw [max_eq_left (le_of_lt (not_le.mp h)),
      inv_mul_cancel₀ (by linarith [not_le.mp h] : ‖y‖ ≠ 0)]

lemma norm_radialUnitSafe_of_half_lt {k : ℕ} {y : Fin k → ℝ} (hy : (1 / 2 : ℝ) < ‖y‖) :
    ‖radialUnitSafe y‖ = 1 := by
  rw [radialUnitSafe_eq_radialUnit hy]
  exact norm_radialUnit (by intro h; rw [h, norm_zero] at hy; linarith)

lemma radialUnitSafe_eq_self_of_norm_eq_one {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ = 1) :
    radialUnitSafe y = y := by
  rw [radialUnitSafe_eq_radialUnit (by rw [hy]; norm_num),
    radialUnit_eq_self_of_norm_eq_one hy]

/-- The radial interpolation between `y` and its radial projection, at parameter `t`. -/
def radialInterp {k : ℕ} (y : Fin k → ℝ) (t : ℝ) : Fin k → ℝ :=
  (1 - t) • y + t • radialUnit y

/-- A globally continuous version of the radial interpolation. -/
def radialInterpSafe {k : ℕ} (y : Fin k → ℝ) (t : ℝ) : Fin k → ℝ :=
  (1 - t) • y + t • radialUnitSafe y

lemma radialInterpSafe_eq_radialInterp {k : ℕ} {y : Fin k → ℝ} (hy : (1 / 2 : ℝ) < ‖y‖) (t : ℝ) :
    radialInterpSafe y t = radialInterp y t := by
  rw [radialInterpSafe, radialInterp, radialUnitSafe_eq_radialUnit hy]

lemma norm_radialInterpSafe_le {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ‖radialInterpSafe y t‖ ≤ 1 := by
  have h1 : ‖radialUnitSafe y‖ ≤ 1 := norm_radialUnitSafe_le_one hy
  calc ‖radialInterpSafe y t‖ ≤ ‖(1 - t) • y‖ + ‖t • radialUnitSafe y‖ := norm_add_le _ _
    _ = (1 - t) * ‖y‖ + t * ‖radialUnitSafe y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    _ ≤ 1 := by nlinarith [norm_nonneg y]

lemma norm_radialInterp_le {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ‖radialInterp y t‖ ≤ 1 := by
  by_cases h0 : y = 0
  · subst h0
    simp [radialInterp, radialUnit]
  · have hy1 : ‖radialUnit y‖ = 1 := norm_radialUnit h0
    calc ‖radialInterp y t‖ ≤ ‖(1 - t) • y‖ + ‖t • radialUnit y‖ := norm_add_le _ _
      _ = (1 - t) * ‖y‖ + t * ‖radialUnit y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg ht0]
      _ = (1 - t) * ‖y‖ + t := by rw [hy1, mul_one]
      _ ≤ 1 := by nlinarith [norm_nonneg y]

lemma radialInterpSafe_zero {k : ℕ} (y : Fin k → ℝ) : radialInterpSafe y 0 = y := by
  simp [radialInterpSafe]

lemma radialInterpSafe_one {k : ℕ} (y : Fin k → ℝ) : radialInterpSafe y 1 = radialUnitSafe y := by
  simp [radialInterpSafe]

lemma radialInterpSafe_eq_self_of_norm_eq_one {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ = 1) (t : ℝ) :
    radialInterpSafe y t = y := by
  rw [radialInterpSafe, radialUnitSafe_eq_self_of_norm_eq_one hy, ← add_smul]
  simp

lemma radialInterpSafe_eq_smul {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    radialInterpSafe y t = ((1 - t) + t * (max ‖y‖ (1 / 2))⁻¹) • y := by
  rw [radialInterpSafe, radialUnitSafe, smul_smul]
  module

lemma one_le_interpCoeff {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (1 - t) + t * (max ‖y‖ (1 / 2 : ℝ))⁻¹ := by
  have h1 : (1 : ℝ) ≤ (max ‖y‖ (1 / 2 : ℝ))⁻¹ := by
    rw [one_le_inv₀ (lt_of_lt_of_le (by norm_num) (le_max_right _ _))]
    exact max_le (by linarith) (by norm_num)
  nlinarith

lemma norm_mul_inv_max_le_one {k : ℕ} (y : Fin k → ℝ) :
    ‖y‖ * (max ‖y‖ (1 / 2 : ℝ))⁻¹ ≤ 1 := by
  by_cases h : ‖y‖ ≤ (1 / 2 : ℝ)
  · rw [max_eq_right h]
    calc ‖y‖ * (1 / 2 : ℝ)⁻¹ ≤ (1 / 2) * (1 / 2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 1 := by norm_num
  · have h2 : (1 / 2 : ℝ) ≤ ‖y‖ := le_of_lt (not_le.mp h)
    rw [max_eq_left h2, mul_inv_cancel₀ (by linarith : ‖y‖ ≠ 0)]

lemma modelCollar_radialInterpSafe {k : ℕ} {y : Fin (k + 1) → ℝ} (hy : y ∈ modelCollar k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : radialInterpSafe y t ∈ modelCollar k := by
  have hcoef : (1 : ℝ) ≤ (1 - t) + t * (max ‖y‖ (1 / 2 : ℝ))⁻¹ :=
    one_le_interpCoeff hy.2 ht0
  have hnorm : ‖radialInterpSafe y t‖
      = ((1 - t) + t * (max ‖y‖ (1 / 2 : ℝ))⁻¹) * ‖y‖ := by
    rw [radialInterpSafe_eq_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    nlinarith [norm_nonneg y, hy.1]
  · rw [hnorm]
    have hb : ‖y‖ * (max ‖y‖ (1 / 2 : ℝ))⁻¹ ≤ 1 := norm_mul_inv_max_le_one y
    nlinarith [norm_nonneg y, hy.2, ht0, ht1, hb]

lemma radialInterp_eq_self_of_norm_eq_one {k : ℕ} {y : Fin k → ℝ} (hy : ‖y‖ = 1) (t : ℝ) :
    radialInterp y t = y := by
  rw [radialInterp, radialUnit_eq_self_of_norm_eq_one hy, ← add_smul]
  simp

/-! ## §4 The step pieces -/

/-- The `n`-skeleton as a set. -/
abbrev skel (C : Set X) [CWComplex C] (n : ℕ) : Set X := (RelCWComplex.skeleton C n : Set X)

lemma skel_subset_skel_succ {n : ℕ} : skel C n ⊆ skel C (n + 1) := by
  intro x hx
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff]
  obtain ⟨m, hm, j, hj⟩ := hx
  have hm' : m ≤ n := by exact_mod_cast hm
  exact ⟨m, (Nat.cast_le (α := ℕ∞)).mpr (by omega), j, hj⟩

/-- The `(n+1)`-skeleton with the centres of its top cells removed. -/
def stepU (C : Set X) [CWComplex C] (n : ℕ) : Set X := skel C (n + 1) \ centres C (n + 1)

/-- The union of the open `(n+1)`-cells. -/
def stepV (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  ⋃ j : RelCWComplex.cell C (n + 1), RelCWComplex.openCell (n + 1) j

/-- The inner closed half-disks of the `(n+1)`-cells. -/
def innerDisk (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  ⋃ j : RelCWComplex.cell C (n + 1),
    RelCWComplex.map (n + 1) j '' Metric.closedBall (0 : Fin (n + 1) → ℝ) (1 / 2)

/-- The *collar space* of the `(n+1)`-skeleton: the `n`-skeleton together with the collars
`1/2 < ‖y‖ ≤ 1` of the top cells. It is an open neighbourhood of the `n`-skeleton in the
`(n+1)`-skeleton that is homotopy equivalent to the `n`-skeleton (see
`Submission.Work.CWTOP.Radial`). -/
def stepCollar (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  skel C n ∪ ⋃ j : RelCWComplex.cell C (n + 1),
    (RelCWComplex.map (n + 1) j '' modelCollar n : Set X)

lemma skel_subset_stepCollar {n : ℕ} : skel C n ⊆ stepCollar C n := fun x hx => Or.inl hx

/-- The space obtained by gluing the `n`-skeleton to the collars of the `(n+1)`-cells. -/
abbrev stepPieces (C : Set X) [CWComplex C] (n : ℕ) : Type :=
  {x : X // x ∈ skel C n} ⊕
    (Σ j : RelCWComplex.cell C (n + 1), {y : Fin (n + 1) → ℝ // y ∈ modelCollar n})

/-- The canonical map from the glued pieces to the collar space. -/
def stepGlue (C : Set X) [CWComplex C] (n : ℕ) : stepPieces C n → {x : X // x ∈ stepCollar C n}
  | Sum.inl ⟨x, hx⟩ => ⟨x, Or.inl hx⟩
  | Sum.inr ⟨j, ⟨y, hy⟩⟩ =>
      ⟨RelCWComplex.map (n + 1) j y, Or.inr (Set.mem_iUnion.mpr ⟨j, y, hy, rfl⟩)⟩

/-- The radial projection of the glued pieces onto the `n`-skeleton. -/
def stepRadialPiece (C : Set X) [CWComplex C] (n : ℕ) : stepPieces C n → {x : X // x ∈ skel C n}
  | Sum.inl ⟨x, hx⟩ => ⟨x, hx⟩
  | Sum.inr ⟨j, ⟨y, hy⟩⟩ =>
      ⟨RelCWComplex.map (n + 1) j (radialUnitSafe y),
        RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := j)
          ⟨radialUnitSafe y, by
            rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
            exact norm_radialUnitSafe_of_half_lt hy.1, rfl⟩⟩

/-- The radial homotopy on the glued pieces, split as a map on the disjoint union of the two
products. -/
def stepHomPieceSum (C : Set X) [CWComplex C] (n : ℕ) :
    (unitInterval × {x : X // x ∈ skel C n}) ⊕
      (Σ j : RelCWComplex.cell C (n + 1),
        {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval) →
    {x : X // x ∈ stepCollar C n}
  | Sum.inl (_, ⟨x, hx⟩) => ⟨x, Or.inl hx⟩
  | Sum.inr ⟨j, ⟨y, hy⟩, t⟩ =>
      ⟨RelCWComplex.map (n + 1) j (radialInterpSafe y (t : ℝ)),
        Or.inr (Set.mem_iUnion.mpr ⟨j, radialInterpSafe y (t : ℝ),
          modelCollar_radialInterpSafe hy t.2.1 t.2.2, rfl⟩)⟩

/-- The distribution homeomorphism used to define the radial homotopy on the glued pieces. -/
noncomputable def stepHomDistrib (C : Set X) [CWComplex C] (n : ℕ) :
    unitInterval × stepPieces C n ≃ₜ
      (unitInterval × {x : X // x ∈ skel C n}) ⊕
        (Σ j : RelCWComplex.cell C (n + 1),
          {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval) :=
  (Homeomorph.prodSumDistrib (X := unitInterval)
      (Y := {x : X // x ∈ skel C n})
      (Z := (Σ j : RelCWComplex.cell C (n + 1),
        {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}))).trans
    (Homeomorph.sumCongr (Homeomorph.refl _)
      ((Homeomorph.prodComm _ _).trans
        (Homeomorph.sigmaProdDistrib (X := fun j : RelCWComplex.cell C (n + 1) =>
          {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}) (Y := unitInterval))))

/-- The radial homotopy on the glued pieces; it is constantly the identity on the `n`-skeleton. -/
noncomputable def stepHomPiece (C : Set X) [CWComplex C] (n : ℕ) :
    unitInterval × stepPieces C n → {x : X // x ∈ stepCollar C n} :=
  stepHomPieceSum C n ∘ stepHomDistrib C n

end Work.CWTOP
