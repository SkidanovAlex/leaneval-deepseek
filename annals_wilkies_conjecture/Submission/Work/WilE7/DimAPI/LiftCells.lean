/-
  WilE7 / DimAPI — the three-cell cylindrical lift of a set in `ℝ^n`.

  For a base set `γ ⊆ ℝ^n`, `liftCells n γ` is the three-element family of cells of `ℝ^{n+1}`
  whose `Fin.init`-image is `γ`:

  * the graph at the level `-1`,
  * the open band `(-1,1)`,
  * the graph at the level `1`.

  These are exactly the cells of the cylindrical decomposition of the closed cylinder
  `{y | Fin.init y ∈ γ ∧ |y (Fin.last n)| ≤ 1}` produced by `Work.WilE7.decomp_of_sections` with
  no sections (`q = 0`); the file records the elementary set-theoretic facts about them:
  membership (`mem_liftCells`), `Fin.init`-images (`finInit_liftCells`), cell-hood
  (`isCell_liftCells`, from `isCell_gr`/`isCell_bd`) and the union (`sUnion_liftCells`).

  `liftFam n C` is the union of `liftCells n γ` over a finite family `C` of base sets; it is the
  family that lifts a cylindrical decomposition of `cubeC n` to one of `cubeC (n+1)`
  (the statement `Work.WilE7.DimAPI.isCylDecompOn_liftFam`, in
  `Submission/Work/WilE7/DimAPI/cylLiftFam.lean`).
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

/-- The three lifted cells over a base set `γ ⊆ ℝ^n`: the graphs at the levels `±1` and the open
band between them. -/
def liftCells (n : ℕ) (γ : Set (Fin n → ℝ)) : Finset (Set (Fin (n+1) → ℝ)) :=
  {{y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = -1},
   {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ -1 < y (Fin.last n) ∧ y (Fin.last n) < 1},
   {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = 1}}

/-- The lift of a finite family of base sets: the union of the three lifted cells of each member. -/
def liftFam (n : ℕ) (C : Finset (Set (Fin n → ℝ))) : Finset (Set (Fin (n+1) → ℝ)) :=
  C.biUnion (liftCells n)

/-- Membership in `liftCells n γ`. -/
theorem mem_liftCells {n : ℕ} {γ : Set (Fin n → ℝ)} {κ : Set (Fin (n+1) → ℝ)} :
    κ ∈ liftCells n γ ↔
      κ = {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = -1} ∨
      κ = {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ -1 < y (Fin.last n) ∧ y (Fin.last n) < 1} ∨
      κ = {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = 1} := by
  simp [liftCells]

/-- Each lifted cell projects onto the base set: `Fin.init '' κ = γ`. -/
theorem finInit_liftCells {n : ℕ} {γ : Set (Fin n → ℝ)} (hγ : γ.Nonempty)
    {κ : Set (Fin (n+1) → ℝ)} (hκ : κ ∈ liftCells n γ) : Fin.init '' κ = γ := by
  rw [mem_liftCells] at hκ
  rcases hκ with rfl | rfl | rfl <;> ext x <;> constructor
  · rintro ⟨z, hz, rfl⟩; exact hz.1
  · intro hx; exact ⟨Fin.snoc x (-1), ⟨by simpa using hx, by simp⟩, by simp⟩
  · rintro ⟨z, hz, rfl⟩; exact hz.1
  · intro hx; exact ⟨Fin.snoc x 0, ⟨by simpa using hx, by simp, by simp⟩, by simp⟩
  · rintro ⟨z, hz, rfl⟩; exact hz.1
  · intro hx; exact ⟨Fin.snoc x 1, ⟨by simpa using hx, by simp⟩, by simp⟩

/-- Every lifted cell over a cell is a cell. -/
theorem isCell_liftCells {n : ℕ} {γ : Set (Fin n → ℝ)} (hγ : WilkiesDesign.IsCell n γ)
    {κ : Set (Fin (n+1) → ℝ)} (hκ : κ ∈ liftCells n γ) : WilkiesDesign.IsCell (n+1) κ := by
  rw [mem_liftCells] at hκ
  rcases hκ with rfl | rfl | rfl
  · exact Work.WilE7.isCell_gr hγ continuousOn_const
  · exact Work.WilE7.isCell_bd hγ continuousOn_const continuousOn_const (fun x _ => by norm_num)
  · exact Work.WilE7.isCell_gr hγ continuousOn_const

/-- The union of the three lifted cells over `γ` is the closed cylinder over `γ`. -/
theorem sUnion_liftCells {n : ℕ} (γ : Set (Fin n → ℝ)) :
    ⋃₀ (liftCells n γ : Set (Set (Fin (n+1) → ℝ)))
      = {y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ |y (Fin.last n)| ≤ 1} := by
  ext z
  constructor
  · rintro ⟨κ, hκ, hz⟩
    rw [Finset.mem_coe, mem_liftCells] at hκ
    rcases hκ with rfl | rfl | rfl
    · exact ⟨hz.1, by rw [hz.2]; norm_num⟩
    · exact ⟨hz.1, abs_le.mpr ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩
    · exact ⟨hz.1, by rw [hz.2]; norm_num⟩
  · rintro ⟨h1, h2⟩
    have hge : -1 ≤ z (Fin.last n) := (abs_le.mp h2).1
    have hle : z (Fin.last n) ≤ 1 := (abs_le.mp h2).2
    rcases lt_or_eq_of_le hge with h | h
    · rcases lt_or_eq_of_le hle with h' | h'
      · exact ⟨{y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ -1 < y (Fin.last n) ∧ y (Fin.last n) < 1},
          by rw [Finset.mem_coe, mem_liftCells]; exact Or.inr (Or.inl rfl), h1, h, h'⟩
      · exact ⟨{y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = 1},
          by rw [Finset.mem_coe, mem_liftCells]; exact Or.inr (Or.inr rfl), h1, h'⟩
    · exact ⟨{y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = -1},
        by rw [Finset.mem_coe, mem_liftCells]; exact Or.inl rfl, h1, h.symm⟩

/-- Membership in the lifted family: `κ` lies over some member of `C`. -/
theorem mem_liftFam {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {κ : Set (Fin (n+1) → ℝ)} :
    κ ∈ liftFam n C ↔ ∃ γ ∈ C, κ ∈ liftCells n γ :=
  Finset.mem_biUnion

end Work.WilE7.DimAPI
