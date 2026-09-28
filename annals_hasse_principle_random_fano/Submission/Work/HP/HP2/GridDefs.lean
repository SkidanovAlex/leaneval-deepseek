import Mathlib
import Submission.Work.HP.Defs

/-!
# Grid counting for a coset of `W ℤ^m` (definitions)

Basic definitions for the lattice-point counting bound `Work.HP.HP2.grid_count_bounds`.

* `fundBox m W` : the half-open fundamental box `∏ᵢ [0, W)` of the lattice `W ℤ^m` in `ℝ^m`.
* `gridVal m W b z` : the point `b + W z` of the coset `b + W ℤ^m`.
* `gridIdx m W b x` : the integer vector `z` with `b + W z ≤ x < b + W (z + 1)` (coordinatewise).
* `gridPt m W b x` : the grid point `b + W * gridIdx m W b x`.
* `gridIn m W b S` : the grid points of the coset that lie in `S` (the set `Λ` of the paper).
* `gridIdxIn m W b S` : the corresponding integer vectors `z`.
-/

set_option autoImplicit false

noncomputable section

open Classical MeasureTheory

namespace Work.HP.HP2

/-- The half-open fundamental box `∏ᵢ [0, W)` of the lattice `W ℤ^m` inside `ℝ^m`. -/
def fundBox (m : ℕ) (W : ℝ) : Set (Fin m → ℝ) := Set.pi Set.univ fun _ => Set.Ico 0 W

/-- The point `b + W z` of the coset `b + W ℤ^m`. -/
def gridVal (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (z : Fin m → ℤ) : Fin m → ℝ :=
  fun i => (b i : ℝ) + (W : ℝ) * (z i : ℝ)

/-- The integer coordinates of the point of the coset `b + W ℤ^m` lying at or below `x`. -/
def gridIdx (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (x : Fin m → ℝ) : Fin m → ℤ :=
  fun i => ⌊(x i - (b i : ℝ)) / (W : ℝ)⌋

/-- The grid point of the coset `b + W ℤ^m` lying at or below `x`. -/
def gridPt (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (x : Fin m → ℝ) : Fin m → ℝ :=
  gridVal m W b (gridIdx m W b x)

/-- The grid points `Λ` of the coset `b + W ℤ^m` that lie in `S`. -/
def gridIn (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {x | x ∈ S ∧ ∃ z : Fin m → ℤ, x = gridVal m W b z}

/-- The integer vectors `z` with `b + W z ∈ S`. -/
def gridIdxIn (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (S : Set (Fin m → ℝ)) : Set (Fin m → ℤ) :=
  {z | gridVal m W b z ∈ S}


/-- The translate `t + fundBox m W` of the fundamental box (a cell of the grid `W ℤ^m`). -/
def gridCell (m : ℕ) (W : ℝ) (t : Fin m → ℝ) : Set (Fin m → ℝ) := (fun y => t + y) '' fundBox m W

lemma mem_gridCell {m : ℕ} {W : ℝ} {t x : Fin m → ℝ} :
    x ∈ gridCell m W t ↔ x - t ∈ fundBox m W := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - t, hx, by simp⟩

lemma gridCell_eq_preimage (m : ℕ) (W : ℝ) (t : Fin m → ℝ) :
    gridCell m W t = (fun y => -t + y) ⁻¹' fundBox m W := by
  ext x
  rw [mem_gridCell]
  simp only [Set.mem_preimage]
  constructor
  · intro h; simpa [sub_eq_add_neg, add_comm] using h
  · intro h; simpa [sub_eq_add_neg, add_comm] using h

lemma gridIn_eq_image (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (S : Set (Fin m → ℝ)) :
    gridIn m W b S = gridVal m W b '' gridIdxIn m W b S := by
  ext x
  constructor
  · rintro ⟨hxS, z, rfl⟩
    exact ⟨z, hxS, rfl⟩
  · rintro ⟨z, hzS, rfl⟩
    exact ⟨hzS, z, rfl⟩

lemma gridVal_injective (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) :
    Function.Injective (gridVal m W b) := by
  intro z z' h
  funext i
  have h1 : (W : ℝ) * (z i : ℝ) = (W : ℝ) * (z' i : ℝ) := by
    have := congrFun h i
    simp only [gridVal] at this
    linarith
  have hW' : (W : ℝ) ≠ 0 := by positivity
  have h2 : (z i : ℝ) = (z' i : ℝ) := mul_left_cancel₀ hW' h1
  exact_mod_cast h2


/-- The number of grid points of the coset lying in `S` equals the number of corresponding
integer vectors `z`. -/
lemma ncard_gridIn_eq (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) (S : Set (Fin m → ℝ)) :
    (gridIn m W b S).ncard = (gridIdxIn m W b S).ncard := by
  rw [gridIn_eq_image, Set.ncard_image_of_injective _ (gridVal_injective m hW b)]

lemma gridPt_eq (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (x : Fin m → ℝ) :
    gridPt m W b x = gridVal m W b (gridIdx m W b x) := rfl

lemma gridPt_mem_coset (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (x : Fin m → ℝ) :
    ∃ z : Fin m → ℤ, gridPt m W b x = gridVal m W b z :=
  ⟨gridIdx m W b x, rfl⟩

end Work.HP.HP2
