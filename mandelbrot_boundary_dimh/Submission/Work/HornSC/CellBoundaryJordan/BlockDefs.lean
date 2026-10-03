import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells

/-!
# Rectangular cell blocks and wall helpers

`RectBlock A a c b d` says that every cell of the lattice rectangle `[a,c) × [b,d)` belongs to
`A`.  The lemmas below are the local input for the proof that `cellUnion A` is open away from the
wall set.

If `z ∈ cellUnion A` and `z ∉ wallSet A` then, near `z`, the cells of `A` fill a whole lattice
rectangle around `z`; the position of `z` in the unit grid dictates *which* rectangle, and the
`block_of_*` lemmas (in the sibling files) record the four cases.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- `RectBlock A a c b d` says: every lattice cell `(p,q)` with `a ≤ p < c` and `b ≤ q < d`
belongs to `A`. -/
def RectBlock (A : Finset (ℤ × ℤ)) (a c b d : ℤ) : Prop :=
  ∀ p q : ℤ, a ≤ p → p < c → b ≤ q → q < d → (p, q) ∈ A

lemma rectBlock_iff {A : Finset (ℤ × ℤ)} {a c b d : ℤ} :
    RectBlock A a c b d ↔ ∀ p q : ℤ, a ≤ p → p < c → b ≤ q → q < d → (p, q) ∈ A :=
  Iff.rfl

/-! ## Extracting a cell of `A` containing `z` -/

lemma exists_cell_mem_of_mem_cellUnion {A : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ cellUnion A) : ∃ p ∈ A, z ∈ cell p := by
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  exact ⟨p, hp, hzp⟩

/-- A cell containing `z` has its first index among `⌊z.re⌋ - 1` and `⌊z.re⌋`. -/
lemma mem_cell_fst_cases {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell p) :
    p.1 = ⌊z.re⌋ ∨ p.1 = ⌊z.re⌋ - 1 := by
  obtain ⟨h1, h2, _, _⟩ := mem_cell.mp hz
  have h1' : p.1 < ⌊z.re⌋ + 1 := by
    have hh : ((p.1 : ℤ) : ℝ) < ((⌊z.re⌋ + 1 : ℤ) : ℝ) := by
      push_cast; linarith [Int.lt_floor_add_one z.re]
    exact_mod_cast hh
  have h2' : ⌊z.re⌋ ≤ p.1 + 1 := by
    have hh : ((⌊z.re⌋ : ℤ) : ℝ) ≤ ((p.1 + 1 : ℤ) : ℝ) := by
      push_cast; linarith [Int.floor_le z.re]
    exact_mod_cast hh
  omega

/-- A cell containing `z` has its second index among `⌊z.im⌋ - 1` and `⌊z.im⌋`. -/
lemma mem_cell_snd_cases {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell p) :
    p.2 = ⌊z.im⌋ ∨ p.2 = ⌊z.im⌋ - 1 := by
  obtain ⟨_, _, h1, h2⟩ := mem_cell.mp hz
  have h1' : p.2 < ⌊z.im⌋ + 1 := by
    have hh : ((p.2 : ℤ) : ℝ) < ((⌊z.im⌋ + 1 : ℤ) : ℝ) := by
      push_cast; linarith [Int.lt_floor_add_one z.im]
    exact_mod_cast hh
  have h2' : ⌊z.im⌋ ≤ p.2 + 1 := by
    have hh : ((⌊z.im⌋ : ℤ) : ℝ) ≤ ((p.2 + 1 : ℤ) : ℝ) := by
      push_cast; linarith [Int.floor_le z.im]
    exact_mod_cast hh
  omega

/-- If `z` is strictly inside its unit column then a cell containing `z` has first index
`⌊z.re⌋`. -/
lemma mem_cell_fst_eq_floor {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell p)
    (h : (⌊z.re⌋ : ℝ) < z.re) : p.1 = ⌊z.re⌋ := by
  rcases mem_cell_fst_cases hz with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨hlo, _, _, _⟩ := mem_cell.mp hz
    have : z.re ≤ (⌊z.re⌋ : ℝ) := by
      have : (p.1 : ℝ) + 1 = (⌊z.re⌋ : ℝ) := by
        rw [h1]; push_cast; ring
      linarith [hlo, (mem_cell.mp hz).2.1]
    linarith

/-- If `z` is strictly inside its unit row then a cell containing `z` has second index
`⌊z.im⌋`. -/
lemma mem_cell_snd_eq_floor {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell p)
    (h : (⌊z.im⌋ : ℝ) < z.im) : p.2 = ⌊z.im⌋ := by
  rcases mem_cell_snd_cases hz with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨_, _, hlo, _⟩ := mem_cell.mp hz
    have : z.im ≤ (⌊z.im⌋ : ℝ) := by
      have : (p.2 : ℝ) + 1 = (⌊z.im⌋ : ℝ) := by
        rw [h1]; push_cast; ring
      linarith [hlo, (mem_cell.mp hz).2.2]
    linarith

/-! ## Wall helpers -/

lemma not_hWallAt_of_mem_hSeg {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} {z : ℂ}
    (hw : z ∉ wallSet A) (h : z ∈ hSeg u) : ¬ hWallAt A u :=
  fun hh => hw (mem_wallSet.mpr (Or.inl ⟨u, hh, h⟩))

lemma not_vWallAt_of_mem_vSeg {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} {z : ℂ}
    (hw : z ∉ wallSet A) (h : z ∈ vSeg u) : ¬ vWallAt A u :=
  fun hh => hw (mem_wallSet.mpr (Or.inr ⟨u, hh, h⟩))

lemma mem_west_of_not_vWallAt {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ}
    (h : ¬ vWallAt A u) (hu : (u.1, u.2) ∈ A) : (u.1 - 1, u.2) ∈ A := by
  by_contra hc
  exact h (Or.inl ⟨hu, hc⟩)

lemma mem_east_of_not_vWallAt {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ}
    (h : ¬ vWallAt A u) (hu : (u.1 - 1, u.2) ∈ A) : (u.1, u.2) ∈ A := by
  by_contra hc
  exact h (Or.inr ⟨hc, hu⟩)

lemma mem_south_of_not_hWallAt {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ}
    (h : ¬ hWallAt A u) (hu : (u.1, u.2) ∈ A) : (u.1, u.2 - 1) ∈ A := by
  by_contra hc
  exact h (Or.inl ⟨hu, hc⟩)

lemma mem_north_of_not_hWallAt {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ}
    (h : ¬ hWallAt A u) (hu : (u.1, u.2 - 1) ∈ A) : (u.1, u.2) ∈ A := by
  by_contra hc
  exact h (Or.inr ⟨hc, hu⟩)

/-! ## Membership in the standard grid segments

These package "the point `z` lies on the grid segment adjacent to its floor cell". -/

lemma mem_vSeg_floor {z : ℂ} (h : z.re = (⌊z.re⌋ : ℝ)) :
    z ∈ vSeg (⌊z.re⌋, ⌊z.im⌋) := by
  rw [mem_vSeg]
  refine ⟨h, Int.floor_le z.im, ?_⟩
  linarith [Int.lt_floor_add_one z.im]

lemma mem_vSeg_floor_below {z : ℂ} (h : z.re = (⌊z.re⌋ : ℝ))
    (h2 : z.im = (⌊z.im⌋ : ℝ)) :
    z ∈ vSeg (⌊z.re⌋, ⌊z.im⌋ - 1) := by
  rw [mem_vSeg]
  refine ⟨h, ?_, ?_⟩
  · push_cast; linarith [Int.floor_le z.im]
  · push_cast; linarith [h2]

lemma mem_hSeg_floor {z : ℂ} (h : z.im = (⌊z.im⌋ : ℝ)) :
    z ∈ hSeg (⌊z.re⌋, ⌊z.im⌋) := by
  rw [mem_hSeg]
  refine ⟨h, Int.floor_le z.re, ?_⟩
  linarith [Int.lt_floor_add_one z.re]

lemma mem_hSeg_floor_left {z : ℂ} (h : z.im = (⌊z.im⌋ : ℝ))
    (h2 : z.re = (⌊z.re⌋ : ℝ)) :
    z ∈ hSeg (⌊z.re⌋ - 1, ⌊z.im⌋) := by
  rw [mem_hSeg]
  refine ⟨h, ?_, ?_⟩
  · push_cast; linarith [Int.floor_le z.re]
  · push_cast; linarith [h2]

end Work.HornSC.CellBoundaryJordan
