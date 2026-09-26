import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.CWComplex.Classical.Basic

set_option warn.classDefReducibility false

open Set Function
open scoped Topology

namespace Commons.Topology.Plane

/-!
# Finite unions of segments in `ℂ` are one-dimensional CW complexes

This file proves the lemma `Commons.Topology.Plane.exists_cwComplex_of_finset_segments`: a finite
union of closed line segments in `ℂ`, whose pairwise intersections are contained in the common
endpoints, is a one-dimensional CW complex.

The proof gives the standard planar-graph cell decomposition: the `0`-cells are the vertices which
are not interior points of any edge, and the `1`-cells are the edges themselves (as ordered pairs),
parametrised by `t ↦ (1 - (t+1)/2) • a + ((t+1)/2) • b` on `Fin 1 → ℝ`.

## Main result

* `Commons.Topology.Plane.exists_cwComplex_of_finset_segments`
-/

/-! ## Geometry of a single segment

Elementary lemmas about `segment` and `openSegment` in `ℂ`, and about the standard parametrisation
of a segment by the unit ball of `Fin 1 → ℝ`.
-/

section SegmentGeometry

variable {a b : ℂ}

lemma notMem_openSegment_left (h : a ≠ b) : a ∉ openSegment ℝ a b := by
  rw [openSegment_eq_image]
  rintro ⟨θ, hθ, heq⟩
  simp only at heq
  have h2 : AffineMap.lineMap a b θ = a := by
    rw [AffineMap.lineMap_apply_module (k := ℝ)]
    exact heq
  exact absurd (((AffineMap.lineMap_eq_left_iff (k := ℝ)).mp h2).resolve_left h) (ne_of_gt hθ.1)

lemma notMem_openSegment_right (h : a ≠ b) : b ∉ openSegment ℝ a b := by
  rw [openSegment_symm]
  exact notMem_openSegment_left h.symm

lemma openSegment_eq_segment_diff (h : a ≠ b) :
    openSegment ℝ a b = segment ℝ a b \ {a, b} := by
  ext z
  constructor
  · intro hz
    refine ⟨openSegment_subset_segment ℝ a b hz, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun hza => notMem_openSegment_left h (hza ▸ hz),
           fun hzb => notMem_openSegment_right h (hzb ▸ hz)⟩
  · rintro ⟨hz, hznot⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hznot
    exact mem_openSegment_of_ne_left_right (Ne.symm hznot.1) (Ne.symm hznot.2) hz

/-- The parametrisation of the segment `[a,b]` on the `1`-dimensional box. -/
noncomputable def segParam (a b : ℂ) : (Fin 1 → ℝ) → ℂ :=
  fun t => AffineMap.lineMap a b ((t 0 + 1) / 2)

lemma segParam_apply (t : Fin 1 → ℝ) : segParam a b t = (1 - (t 0 + 1)/2) • a + ((t 0 + 1)/2) • b := by
  simp [segParam, AffineMap.lineMap_apply_module]

lemma mem_ball_fin1 (x : Fin 1 → ℝ) : x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔ |x 0| < 1 := by
  rw [Metric.mem_ball, dist_eq_norm]
  simp [Pi.norm_def]

lemma mem_closedBall_fin1 (x : Fin 1 → ℝ) : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 ↔ |x 0| ≤ 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp [Pi.norm_def]

lemma mem_sphere_fin1 (x : Fin 1 → ℝ) : x ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 ↔ |x 0| = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [Pi.norm_def]

lemma sphere_fin0 : Metric.sphere (0 : Fin 0 → ℝ) 1 = ∅ := by
  ext x
  simp only [Metric.mem_sphere, mem_empty_iff_false, iff_false, dist_eq_norm]
  rw [show x - 0 = 0 from Subsingleton.elim _ _, norm_zero]
  norm_num

lemma segParam_image_closedBall (a b : ℂ) :
    segParam a b '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = segment ℝ a b := by
  refine subset_antisymm ?_ ?_
  · rintro z ⟨t, ht, rfl⟩
    rw [mem_closedBall_fin1, abs_le] at ht
    rw [segment_eq_image_lineMap (𝕜 := ℝ)]
    exact mem_image_of_mem _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro z hz
    rw [segment_eq_image_lineMap (𝕜 := ℝ)] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨![2*s - 1], ?_, ?_⟩
    · rw [mem_closedBall_fin1, abs_le]
      simp only [Matrix.cons_val_fin_one]
      constructor <;> linarith [hs.1, hs.2]
    · simp only [segParam, Matrix.cons_val_fin_one]
      rw [show (2*s - 1 + 1)/2 = s by ring]

lemma segParam_image_ball (a b : ℂ) :
    segParam a b '' Metric.ball (0 : Fin 1 → ℝ) 1 = openSegment ℝ a b := by
  refine subset_antisymm ?_ ?_
  · rintro z ⟨t, ht, rfl⟩
    rw [mem_ball_fin1, abs_lt] at ht
    rw [openSegment_eq_image_lineMap (𝕜 := ℝ)]
    exact mem_image_of_mem _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro z hz
    rw [openSegment_eq_image_lineMap (𝕜 := ℝ)] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨![2*s - 1], ?_, ?_⟩
    · rw [mem_ball_fin1, abs_lt]
      simp only [Matrix.cons_val_fin_one]
      constructor <;> linarith [hs.1, hs.2]
    · simp only [segParam, Matrix.cons_val_fin_one]
      rw [show (2*s - 1 + 1)/2 = s by ring]

lemma segParam_image_sphere (a b : ℂ) :
    segParam a b '' Metric.sphere (0 : Fin 1 → ℝ) 1 = {a, b} := by
  refine subset_antisymm ?_ ?_
  · rintro z ⟨t, ht, rfl⟩
    rw [mem_sphere_fin1, abs_eq zero_le_one] at ht
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases ht with h | h
    · right
      change AffineMap.lineMap a b ((t 0 + 1)/2) = b
      have h1 : ((t 0 + 1)/2 : ℝ) = 1 := by rw [h]; norm_num
      rw [h1]; exact AffineMap.lineMap_apply_one a b
    · left
      change AffineMap.lineMap a b ((t 0 + 1)/2) = a
      have h1 : ((t 0 + 1)/2 : ℝ) = 0 := by rw [h]; norm_num
      rw [h1]; exact AffineMap.lineMap_apply_zero a b
  · rintro z (rfl | rfl)
    · exact ⟨![-1], by rw [mem_sphere_fin1]; simp [Matrix.cons_val_fin_one],
        by simp [segParam, Matrix.cons_val_fin_one]⟩
    · exact ⟨![1], by rw [mem_sphere_fin1]; simp [Matrix.cons_val_fin_one],
        by simp [segParam, Matrix.cons_val_fin_one]⟩

lemma lineMap_sub_div (a b : ℂ) (h : a ≠ b) (s : ℝ) :
    (AffineMap.lineMap a b s - a) / (b - a) = (s : ℂ) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hnum : AffineMap.lineMap a b s - a = (s : ℂ) * (b - a) := by
    rw [AffineMap.lineMap_apply_module (k := ℝ), Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hnum, mul_div_cancel_right₀ _ hba]

end SegmentGeometry

/-! ## The cell decomposition -/

section CellDecomposition

variable (V : Finset ℂ) (E : Finset (ℂ × ℂ))

/-- The vertices of `V` that are not interior points of any edge of `E`.  These are the `0`-cells
of the CW structure. -/
def verts : Set ℂ := {v | v ∈ V ∧ ∀ e ∈ E, v ∉ openSegment ℝ e.1 e.2}

lemma mem_verts {v : ℂ} :
    v ∈ verts V E ↔ v ∈ V ∧ ∀ e ∈ E, v ∉ openSegment ℝ e.1 e.2 := Iff.rfl

lemma verts_subset : verts V E ⊆ (V : Set ℂ) := fun _ hv => hv.1

lemma verts_finite : (verts V E).Finite := V.finite_toSet.subset (verts_subset V E)

lemma mem_segments_of_mem_of_notMem_verts {v : ℂ} (hv : v ∈ V) (hv' : v ∉ verts V E) :
    v ∈ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  have h2 : ¬ ∀ e ∈ E, v ∉ openSegment ℝ e.1 e.2 := fun hc => hv' ⟨hv, hc⟩
  push Not at h2
  obtain ⟨e, he, hz⟩ := h2
  refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, ?_⟩⟩
  exact openSegment_subset_segment ℝ e.1 e.2 hz

lemma left_mem_verts {hV : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V} {hne : ∀ e ∈ E, e.1 ≠ e.2}
    {hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)}
    {e : ℂ × ℂ} (he : e ∈ E) : e.1 ∈ verts V E := by
  refine ⟨(hV e he).1, fun e' he' => ?_⟩
  intro hz
  have hseg : e.1 ∈ segment ℝ e'.1 e'.2 := openSegment_subset_segment ℝ _ _ hz
  by_cases h : e = e'
  · rw [h] at hz
    exact notMem_openSegment_left (hne e' he') hz
  · have h3 := hdisj e he e' he' h ⟨left_mem_segment ℝ e.1 e.2, hseg⟩
    rcases h3.2 with h' | h'
    · rw [h'] at hz
      exact notMem_openSegment_left (hne e' he') hz
    · rw [h'] at hz
      exact notMem_openSegment_right (hne e' he') hz

lemma right_mem_verts {hV : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V} {hne : ∀ e ∈ E, e.1 ≠ e.2}
    {hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)}
    {e : ℂ × ℂ} (he : e ∈ E) : e.2 ∈ verts V E := by
  refine ⟨(hV e he).2, fun e' he' => ?_⟩
  intro hz
  have hseg : e.2 ∈ segment ℝ e'.1 e'.2 := openSegment_subset_segment ℝ _ _ hz
  by_cases h : e = e'
  · rw [h] at hz
    exact notMem_openSegment_right (hne e' he') hz
  · have h3 := hdisj e he e' he' h ⟨right_mem_segment ℝ e.1 e.2, hseg⟩
    rcases h3.2 with h' | h'
    · rw [h'] at hz
      exact notMem_openSegment_left (hne e' he') hz
    · rw [h'] at hz
      exact notMem_openSegment_right (hne e' he') hz

/-- The cell types: `0`-cells are the vertices of `verts V E`, `1`-cells are the elements of `E`
and there are no higher dimensional cells. -/
abbrev cellType : ℕ → Type
  | 0 => {v : ℂ // v ∈ verts V E}
  | 1 => {e : ℂ × ℂ // e ∈ E}
  | _ + 2 => Empty

lemma cellType_isEmpty {n : ℕ} (hn : 2 ≤ n) : IsEmpty (cellType V E n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  subst hk
  rw [show 2 + k = k + 2 from Nat.add_comm 2 k]
  exact ⟨fun x => x.elim⟩

lemma cellType_zero_eq : cellType V E 0 = {v : ℂ // v ∈ verts V E} := rfl

/-- The characteristic map of a `0`-cell: the constant map at the vertex. -/
noncomputable def vertMap (v : ℂ) : PartialEquiv (Fin 0 → ℝ) ℂ where
  toFun _ := v
  invFun _ := 0
  source := Metric.ball (0 : Fin 0 → ℝ) 1
  target := {v}
  map_source' := by intro x _; exact mem_singleton v
  map_target' := by
    intro y hy
    rw [mem_singleton_iff] at hy
    subst hy
    rw [Metric.mem_ball, dist_self]
    norm_num
  left_inv' := by intro x _; exact Subsingleton.elim _ _
  right_inv' := by intro y hy; rw [mem_singleton_iff] at hy; subst hy; rfl

/-- The characteristic map of the `1`-cell with endpoints `a` and `b`, which parametrises the
segment `[a,b]` by the unit ball of `Fin 1 → ℝ`. -/
noncomputable def edgeMap (a b : ℂ) (h : a ≠ b) : PartialEquiv (Fin 1 → ℝ) ℂ where
  toFun t := segParam a b t
  invFun z := ![2 * ((z - a) / (b - a)).re - 1]
  source := Metric.ball (0 : Fin 1 → ℝ) 1
  target := openSegment ℝ a b
  map_source' := by
    intro t ht
    rw [mem_ball_fin1, abs_lt] at ht
    rw [← segParam_image_ball, mem_image]
    exact ⟨t, by rw [mem_ball_fin1, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  map_target' := by
    intro z hz
    rw [openSegment_eq_image_lineMap (𝕜 := ℝ)] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rw [mem_ball_fin1, abs_lt]
    simp only [Matrix.cons_val_fin_one]
    rw [lineMap_sub_div a b h s, Complex.ofReal_re]
    constructor <;> linarith [hs.1, hs.2]
  left_inv' := by
    intro t ht
    rw [mem_ball_fin1, abs_lt] at ht
    funext i
    rw [show i = 0 from Subsingleton.elim i 0]
    simp only [segParam, Matrix.cons_val_fin_one]
    rw [lineMap_sub_div a b h ((t 0 + 1)/2), Complex.ofReal_re]
    ring
  right_inv' := by
    intro z hz
    rw [openSegment_eq_image_lineMap (𝕜 := ℝ)] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    simp only [segParam, Matrix.cons_val_fin_one]
    rw [lineMap_sub_div a b h s, Complex.ofReal_re]
    norm_num

noncomputable def cellMap (hne : ∀ e ∈ E, e.1 ≠ e.2) :
    (n : ℕ) → cellType V E n → PartialEquiv (Fin n → ℝ) ℂ
  | 0, v => vertMap v.1
  | 1, e => edgeMap e.1.1 e.1.2 (hne e.1 e.2)
  | _ + 2, i => i.elim

variable {hne : ∀ e ∈ E, e.1 ≠ e.2}

lemma cellMap_zero (v : cellType V E 0) : cellMap V E hne 0 v = vertMap v.1 := rfl

lemma cellMap_one (e : cellType V E 1) :
    cellMap V E hne 1 e = edgeMap e.1.1 e.1.2 (hne e.1 e.2) := rfl

lemma cellMap_image_ball_zero (v : cellType V E 0) :
    (cellMap V E hne 0 v) '' Metric.ball (0 : Fin 0 → ℝ) 1 = {v.1} := by
  rw [cellMap_zero]
  exact (vertMap v.1).image_source_eq_target

lemma cellMap_image_closedBall_zero (v : cellType V E 0) :
    (cellMap V E hne 0 v) '' Metric.closedBall (0 : Fin 0 → ℝ) 1 = {v.1} := by
  have h : (vertMap v.1) '' Metric.ball (0 : Fin 0 → ℝ) 1 = {v.1} :=
    (vertMap v.1).image_source_eq_target
  have h2 : Metric.closedBall (0 : Fin 0 → ℝ) 1 = Metric.ball (0 : Fin 0 → ℝ) 1 := by
    ext x
    rw [show x = 0 from Subsingleton.elim x 0]
    simp [Metric.mem_ball, Metric.mem_closedBall]
  rw [cellMap_zero, h2, h]

lemma cellMap_image_sphere_zero (v : cellType V E 0) :
    (cellMap V E hne 0 v) '' Metric.sphere (0 : Fin 0 → ℝ) 1 = ∅ := by
  rw [sphere_fin0, image_empty]

lemma cellMap_image_ball_one (e : cellType V E 1) :
    (cellMap V E hne 1 e) '' Metric.ball (0 : Fin 1 → ℝ) 1 = openSegment ℝ e.1.1 e.1.2 := by
  rw [cellMap_one]
  exact (edgeMap e.1.1 e.1.2 (hne e.1 e.2)).image_source_eq_target

lemma cellMap_image_closedBall_one (e : cellType V E 1) :
    (cellMap V E hne 1 e) '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = segment ℝ e.1.1 e.1.2 := by
  rw [cellMap_one, edgeMap, segParam_image_closedBall]

lemma cellMap_image_sphere_one (e : cellType V E 1) :
    (cellMap V E hne 1 e) '' Metric.sphere (0 : Fin 1 → ℝ) 1 = {e.1.1, e.1.2} := by
  rw [cellMap_one, edgeMap, segParam_image_sphere]

end CellDecomposition

section Assembly

open scoped Classical

variable {V : Finset ℂ} {E : Finset (ℂ × ℂ)}
variable {hV : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V} {hne : ∀ e ∈ E, e.1 ≠ e.2}
variable {hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)}

lemma disjoint_cellMap_zero_zero (h : ∀ e ∈ E, e.1 ≠ e.2)
    {ix iy : cellType V E 0} (hxy : ix ≠ iy) :
    Disjoint ((cellMap V E h 0 ix) '' Metric.ball (0 : Fin 0 → ℝ) 1)
      ((cellMap V E h 0 iy) '' Metric.ball (0 : Fin 0 → ℝ) 1) := by
  rw [cellMap_image_ball_zero, cellMap_image_ball_zero, Set.disjoint_singleton_left]
  simp only [mem_singleton_iff]
  exact fun hv => hxy (Subtype.ext hv)

lemma disjoint_cellMap_zero_one (h : ∀ e ∈ E, e.1 ≠ e.2)
    {ix : cellType V E 0} {ey : cellType V E 1} :
    Disjoint ((cellMap V E h 0 ix) '' Metric.ball (0 : Fin 0 → ℝ) 1)
      ((cellMap V E h 1 ey) '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  rw [cellMap_image_ball_zero, cellMap_image_ball_one, Set.disjoint_singleton_left]
  exact ix.2.2 ey.1 ey.2

lemma disjoint_cellMap_one_zero (h : ∀ e ∈ E, e.1 ≠ e.2)
    {ex : cellType V E 1} {iy : cellType V E 0} :
    Disjoint ((cellMap V E h 1 ex) '' Metric.ball (0 : Fin 1 → ℝ) 1)
      ((cellMap V E h 0 iy) '' Metric.ball (0 : Fin 0 → ℝ) 1) :=
  (disjoint_cellMap_zero_one h (V := V) (E := E) (ix := iy) (ey := ex)).symm

lemma disjoint_cellMap_one_one (h : ∀ e ∈ E, e.1 ≠ e.2)
    (hd : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ))
    {ex ey : cellType V E 1} (hxy : ex.1 ≠ ey.1) :
    Disjoint ((cellMap V E h 1 ex) '' Metric.ball (0 : Fin 1 → ℝ) 1)
      ((cellMap V E h 1 ey) '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  rw [cellMap_image_ball_one, cellMap_image_ball_one, Set.disjoint_left]
  intro z hz1 hz2
  have h1 : z ∈ segment ℝ ex.1.1 ex.1.2 := openSegment_subset_segment ℝ _ _ hz1
  have h2 : z ∈ segment ℝ ey.1.1 ey.1.2 := openSegment_subset_segment ℝ _ _ hz2
  have h3 := hd ex.1 ex.2 ey.1 ey.2 hxy ⟨h1, h2⟩
  have hne1 : ex.1.1 ≠ ex.1.2 := h ex.1 ex.2
  have hne2 : ey.1.1 ≠ ey.1.2 := h ey.1 ey.2
  rcases h3.1 with h' | h'
  · rw [h'] at hz1
    exact notMem_openSegment_left hne1 hz1
  · rw [h'] at hz1
    exact notMem_openSegment_right hne1 hz1

lemma iUnion_cellType_eq (f : ∀ n, cellType V E n → Set ℂ) :
    (⋃ n, ⋃ j : cellType V E n, f n j)
      = (⋃ j : cellType V E 0, f 0 j) ∪ (⋃ j : cellType V E 1, f 1 j) := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨j, hx⟩ := hx
    match n, j with
    | 0, j => exact Or.inl (Set.mem_iUnion.mpr ⟨j, hx⟩)
    | 1, j => exact Or.inr (Set.mem_iUnion.mpr ⟨j, hx⟩)
    | _+2, j => exact j.elim
  · rintro x (hx | hx)
    · rw [Set.mem_iUnion] at hx
      obtain ⟨j, hx⟩ := hx
      exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨j, hx⟩⟩
    · rw [Set.mem_iUnion] at hx
      obtain ⟨j, hx⟩ := hx
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨j, hx⟩⟩

lemma iUnion_closedCell_zero (h : ∀ e ∈ E, e.1 ≠ e.2) :
    (⋃ j : cellType V E 0, (cellMap V E h 0 j) '' Metric.closedBall (0 : Fin 0 → ℝ) 1)
      = (verts V E) := by
  refine subset_antisymm ?_ ?_
  · rintro x hx
    simp only [Set.mem_iUnion, mem_image] at hx
    obtain ⟨j, t, ht, hx⟩ := hx
    rw [cellMap_zero] at hx
    have hx' : (j.1 : ℂ) = x := hx
    rw [← hx']
    exact j.2
  · intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [cellMap_image_closedBall_zero]
    exact mem_singleton x

lemma iUnion_closedCell_one (h : ∀ e ∈ E, e.1 ≠ e.2) :
    (⋃ j : cellType V E 1, (cellMap V E h 1 j) '' Metric.closedBall (0 : Fin 1 → ℝ) 1)
      = ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  refine subset_antisymm ?_ ?_
  · rintro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨j, hx⟩ := hx
    rw [cellMap_image_closedBall_one] at hx
    exact mem_iUnion.mpr ⟨j.1, mem_iUnion.mpr ⟨j.2, hx⟩⟩
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨e, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨he, hx⟩ := hx
    refine Set.mem_iUnion.mpr ⟨⟨e, he⟩, ?_⟩
    rwa [cellMap_image_closedBall_one]

/-- The CW complex structure on a finite union of segments: `0`-cells are the vertices of
`verts V E`, `1`-cells are the elements of `E`. -/
noncomputable def cwComplex (V : Finset ℂ) (E : Finset (ℂ × ℂ))
    (hV : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) (hne : ∀ e ∈ E, e.1 ≠ e.2)
    (hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)) :
    Topology.CWComplex (X := ℂ) ((V : Set ℂ) ∪ ⋃ e ∈ E, segment ℝ e.1 e.2) where
  cell := cellType V E
  map := cellMap V E hne
  source_eq := by
    intro n i
    match n, i with
    | 0, v => rfl
    | 1, e => rfl
    | _ + 2, i => exact i.elim
  continuousOn := by
    intro n i
    match n, i with
    | 0, v => exact continuousOn_const
    | 1, e =>
        have hcont : Continuous (fun t : Fin 1 → ℝ => segParam e.1.1 e.1.2 t) := by
          simp only [segParam]
          fun_prop
        exact hcont.continuousOn
    | _ + 2, i => exact i.elim
  continuousOn_symm := by
    intro n i
    match n, i with
    | 0, v => exact continuousOn_const
    | 1, e =>
        apply Continuous.continuousOn
        have h1 : Continuous fun z : ℂ => (z - e.1.1) / (e.1.2 - e.1.1) :=
          (continuous_id.sub continuous_const).div_const _
        have h2 : Continuous fun z : ℂ => 2 * (((z - e.1.1) / (e.1.2 - e.1.1)).re) - 1 :=
          (continuous_const.mul (Complex.continuous_re.comp h1)).sub continuous_const
        have h3 : Continuous fun z : ℂ =>
            (![2 * ((z - e.1.1) / (e.1.2 - e.1.1)).re - 1] : Fin 1 → ℝ) := by
          apply continuous_pi
          intro i
          fin_cases i
          simpa [Matrix.cons_val_fin_one] using h2
        exact h3
    | _ + 2, i => exact i.elim
  pairwiseDisjoint' := by
    intro x _ y _ hxy
    obtain ⟨nx, ix⟩ := x
    obtain ⟨ny, iy⟩ := y
    rw [Function.onFun_apply]
    have hnx : nx ≤ 1 := by
      by_contra h
      push Not at h
      exact (cellType_isEmpty V E (by omega : 2 ≤ nx)).false ix
    have hny : ny ≤ 1 := by
      by_contra h
      push Not at h
      exact (cellType_isEmpty V E (by omega : 2 ≤ ny)).false iy
    interval_cases nx <;> interval_cases ny
    · exact disjoint_cellMap_zero_zero hne
        (fun h => hxy (congrArg (fun j => (⟨0, j⟩ : Σ n, cellType V E n)) h))
    · exact disjoint_cellMap_zero_one hne
    · exact disjoint_cellMap_one_zero hne
    · exact disjoint_cellMap_one_one hne hdisj
        (fun h => hxy (congrArg (fun j => (⟨1, j⟩ : Σ n, cellType V E n)) (Subtype.ext h)))
  mapsTo' := by
    intro n i
    match n, i with
    | 0, v =>
        refine ⟨fun _ => ∅, ?_⟩
        intro x hx
        rw [sphere_fin0] at hx
        exact absurd hx (notMem_empty x)
    | 1, e =>
        have hW1 : e.1.1 ∈ verts V E :=
          left_mem_verts (V := V) (E := E) (hV := hV) (hne := hne) (hdisj := hdisj) e.2
        have hW2 : e.1.2 ∈ verts V E :=
          right_mem_verts (V := V) (E := E) (hV := hV) (hne := hne) (hdisj := hdisj) e.2
        refine ⟨fun m => if h : m = 0 then
            h.symm ▸ ({⟨e.1.1, hW1⟩, ⟨e.1.2, hW2⟩} : Finset (cellType V E 0))
          else ∅, ?_⟩
        rw [mapsTo_iff_image_subset, cellMap_image_sphere_one]
        rintro z (rfl | rfl)
        · refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by norm_num, mem_iUnion.mpr ?_⟩⟩
          refine ⟨⟨e.1.1, hW1⟩, mem_iUnion.mpr ⟨by simp, ?_⟩⟩
          rw [cellMap_image_closedBall_zero]
          exact mem_singleton e.1.1
        · refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by norm_num, mem_iUnion.mpr ?_⟩⟩
          refine ⟨⟨e.1.2, hW2⟩, mem_iUnion.mpr ⟨by simp, ?_⟩⟩
          rw [cellMap_image_closedBall_zero]
          exact mem_singleton e.1.2
    | _ + 2, i => exact i.elim
  closed' := by
    intro A hA hcl
    have hcover : (verts V E : Set ℂ) ∪ (⋃ e ∈ E, segment ℝ e.1 e.2)
        = (V : Set ℂ) ∪ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
      refine subset_antisymm ?_ ?_
      · rintro x (hx | hx)
        · exact Or.inl hx.1
        · exact Or.inr hx
      · rintro x (hx | hx)
        · by_cases h : x ∈ verts V E
          · exact Or.inl h
          · exact Or.inr (mem_segments_of_mem_of_notMem_verts V E hx h)
        · exact Or.inr hx
    have hAeq : A = (A ∩ (verts V E : Set ℂ)) ∪ (A ∩ ⋃ e ∈ E, segment ℝ e.1 e.2) := by
      refine subset_antisymm ?_ ?_
      · intro x hx
        have hxC : x ∈ (verts V E : Set ℂ) ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) := by
          rw [hcover]
          exact hA hx
        rcases hxC with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (hx | hx)
        · exact hx.1
        · exact hx.1
    rw [hAeq]
    apply IsClosed.union
    · have h1 : A ∩ (verts V E : Set ℂ)
          = ⋃ v ∈ (verts V E : Set ℂ), A ∩ ({v} : Set ℂ) := by
        ext x
        constructor
        · rintro ⟨hx, hv⟩
          exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hv, ⟨hx, mem_singleton x⟩⟩⟩
        · intro hx
          rcases mem_iUnion.mp hx with ⟨v, hx⟩
          rcases mem_iUnion.mp hx with ⟨hv, hx⟩
          refine ⟨hx.1, ?_⟩
          rw [show x = v from by simpa using hx.2]
          exact hv
      rw [h1]
      exact (verts_finite V E).isClosed_biUnion (fun v hv => by
        have h := hcl 0 ⟨v, hv⟩
        rwa [cellMap_image_closedBall_zero] at h)
    · have h2 : A ∩ (⋃ e ∈ E, segment ℝ e.1 e.2)
          = ⋃ e ∈ E, A ∩ segment ℝ e.1 e.2 := by
        ext x
        simp only [mem_inter_iff, mem_iUnion]
        constructor
        · rintro ⟨hx, e, he, hxe⟩
          exact ⟨e, he, hx, hxe⟩
        · rintro ⟨e, he, hx, hxe⟩
          exact ⟨hx, e, he, hxe⟩
      rw [h2]
      exact isClosed_biUnion_finset (fun e he => by
        have h := hcl 1 ⟨e, he⟩
        rwa [cellMap_image_closedBall_one] at h)
  union' := by
    rw [iUnion_cellType_eq (V := V) (E := E)
          (fun n j => (cellMap V E hne n j) '' Metric.closedBall 0 1),
      iUnion_closedCell_zero (V := V) (E := E) hne,
      iUnion_closedCell_one (V := V) (E := E) hne]
    refine subset_antisymm ?_ ?_
    · rintro x (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx
    · rintro x (hx | hx)
      · by_cases h : x ∈ verts V E
        · exact Or.inl h
        · exact Or.inr (mem_segments_of_mem_of_notMem_verts V E hx h)
      · exact Or.inr hx

end Assembly

open Set

/-- A finite union of closed line segments in `ℂ` which pairwise meet only in common endpoints
is a one-dimensional CW complex: the vertices (the endpoints) are the 0-cells and the segments
are the 1-cells.  Here `V` is the finite set of vertices and `E` the finite set of edges
(given by their endpoints). -/
theorem exists_cwComplex_of_finset_segments
    (V : Finset ℂ) (E : Finset (ℂ × ℂ))
    (hV : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hne : ∀ e ∈ E, e.1 ≠ e.2)
    (hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
        ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)) :
    ∃ (hC : Topology.CWComplex (X := ℂ) ((V : Set ℂ) ∪ ⋃ e ∈ E, segment ℝ e.1 e.2)),
      ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell ℂ _ _ hC n) := by
  refine ⟨cwComplex V E hV hne hdisj, ?_⟩
  intro n hn
  exact cellType_isEmpty V E hn

end Commons.Topology.Plane