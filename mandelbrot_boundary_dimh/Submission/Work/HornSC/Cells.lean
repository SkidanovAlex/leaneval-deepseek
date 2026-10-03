import Mathlib

/-!
# Unit cells of the integer lattice in `ℂ`

Vocabulary for the polyomino argument of `Work.HornSC.exists_jordan_curve_of_gap`.
-/

namespace Work.HornSC

open Set

/-- The closed unit cell of the integer lattice at `p : ℤ × ℤ`. -/
def cell (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1 ∧
           (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1}

/-- The union of a finite family of lattice cells. -/
def cellUnion (A : Finset (ℤ × ℤ)) : Set ℂ := ⋃ p ∈ A, cell p

/-- Translation of lattice indices. -/
def shiftIdx (v : ℤ × ℤ) : (ℤ × ℤ) → (ℤ × ℤ) := fun p => (p.1 + v.1, p.2 + v.2)

lemma shiftIdx_injective (v : ℤ × ℤ) : Function.Injective (shiftIdx v) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftIdx, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- The translate of a finite family of lattice cells, as an embedding of index sets. -/
def shiftEmb (v : ℤ × ℤ) : (ℤ × ℤ) ↪ (ℤ × ℤ) := ⟨shiftIdx v, shiftIdx_injective v⟩

/-- The translate of a finite family of lattice cells. -/
def shift (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Finset (ℤ × ℤ) := A.map (shiftEmb v)

lemma mem_shift {A : Finset (ℤ × ℤ)} {v q : ℤ × ℤ} :
    q ∈ shift A v ↔ ∃ p ∈ A, shiftIdx v p = q := by
  simp [shift, shiftEmb, Finset.mem_map]

/-- The `3 × 3` dilation of a finite family of lattice cells. -/
def dil3 (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  A.biUnion fun p => (Finset.Icc (p.1 - 1) (p.1 + 1)) ×ˢ (Finset.Icc (p.2 - 1) (p.2 + 1))

lemma mem_dil3 {A : Finset (ℤ × ℤ)} {q : ℤ × ℤ} :
    q ∈ dil3 A ↔ ∃ p ∈ A, |q.1 - p.1| ≤ 1 ∧ |q.2 - p.2| ≤ 1 := by
  simp only [dil3, Finset.mem_biUnion, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨p, hp, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨p, hp, ?_, ?_⟩
    · rw [abs_le]; exact ⟨by omega, by omega⟩
    · rw [abs_le]; exact ⟨by omega, by omega⟩
  · rintro ⟨p, hp, h1, h2⟩
    rw [abs_le] at h1 h2
    exact ⟨p, hp, ⟨by omega, by omega⟩, by omega, by omega⟩

lemma mem_cell {p : ℤ × ℤ} {z : ℂ} :
    z ∈ cell p ↔ (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1 := Iff.rfl

lemma cell_nonempty (p : ℤ × ℤ) : (cell p).Nonempty :=
  ⟨⟨(p.1 : ℝ) + 1 / 2, (p.2 : ℝ) + 1 / 2⟩,
    mem_cell.mpr ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

lemma isClosed_cell (p : ℤ × ℤ) : IsClosed (cell p) := by
  have h1 : IsClosed {z : ℂ | (p.1 : ℝ) ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ (p.1 : ℝ) + 1} :=
    isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | (p.2 : ℝ) ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ (p.2 : ℝ) + 1} :=
    isClosed_le Complex.continuous_im continuous_const
  have h := h1.inter (h2.inter (h3.inter h4))
  convert h using 1
  ext z
  simp only [cell, Set.mem_inter_iff, Set.mem_ofPred_eq]

lemma isCompact_cell (p : ℤ × ℤ) : IsCompact (cell p) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_cell p, ?_⟩
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (|(p.1 : ℝ)| + |(p.2 : ℝ)|) + 2)) ?_
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := mem_cell.mp hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h5 : |z.re| ≤ |(p.1 : ℝ)| + 1 := by
    rw [abs_le]; constructor <;> linarith [neg_abs_le (p.1 : ℝ), le_abs_self (p.1 : ℝ)]
  have h6 : |z.im| ≤ |(p.2 : ℝ)| + 1 := by
    rw [abs_le]; constructor <;> linarith [neg_abs_le (p.2 : ℝ), le_abs_self (p.2 : ℝ)]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |(p.1 : ℝ)| + |(p.2 : ℝ)| + 2 := by linarith

lemma isClosed_cellUnion (A : Finset (ℤ × ℤ)) : IsClosed (cellUnion A) :=
  isClosed_biUnion_finset fun p _ => isClosed_cell p

lemma isCompact_cellUnion (A : Finset (ℤ × ℤ)) : IsCompact (cellUnion A) :=
  Finset.isCompact_biUnion A fun p _ => isCompact_cell p

lemma cell_subset_cellUnion {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ A) :
    cell p ⊆ cellUnion A := fun _ hz => Set.mem_iUnion₂.mpr ⟨p, hp, hz⟩

lemma cellUnion_mono {A B : Finset (ℤ × ℤ)} (h : A ⊆ B) : cellUnion A ⊆ cellUnion B :=
  fun _ hz => by
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨p, h hp, hzp⟩

lemma self_subset_dil3 (A : Finset (ℤ × ℤ)) : A ⊆ dil3 A := by
  intro p hp
  rw [mem_dil3]
  exact ⟨p, hp, by simp, by simp⟩

lemma cellUnion_subset_dil3 (A : Finset (ℤ × ℤ)) : cellUnion A ⊆ cellUnion (dil3 A) :=
  cellUnion_mono (self_subset_dil3 A)

/-- `noPinchAt A v` says: at the lattice point `v`, the cells of `A` incident with `v` are not
exactly the two diagonally opposite ones. -/
def noPinchAt (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Prop :=
  ¬ (((v.1 - 1, v.2 - 1) ∈ A ∧ (v.1, v.2) ∈ A ∧ (v.1, v.2 - 1) ∉ A ∧ (v.1 - 1, v.2) ∉ A) ∨
     ((v.1 - 1, v.2) ∈ A ∧ (v.1, v.2 - 1) ∈ A ∧ (v.1, v.2) ∉ A ∧ (v.1 - 1, v.2 - 1) ∉ A))

/-- The polyomino `A` has no pinch points. -/
def NoPinch (A : Finset (ℤ × ℤ)) : Prop := ∀ v : ℤ × ℤ, noPinchAt A v

end Work.HornSC
