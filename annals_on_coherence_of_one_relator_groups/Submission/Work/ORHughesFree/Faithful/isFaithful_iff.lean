import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix

namespace Work.ORHughesFree.Faithful

open Matrix

/-- A `1 × 1` matrix is zero exactly when its entry is zero. -/
private theorem oneByOne_eq_zero_iff {R : Type*} [Zero R] {a : R} :
    oneByOne a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simpa [oneByOne] using h00
  · intro h
    ext i j
    simpa [oneByOne, h]

/-- A matrix is nonzero exactly when it has a nonzero entry. -/
private theorem ne_zero_iff_exists_entry {R : Type*} [Zero R] {n m : ℕ}
    {A : Matrix (Fin n) (Fin m) R} : A ≠ 0 ↔ ∃ i j, A i j ≠ 0 := by
  constructor
  · intro hA
    by_contra hc
    push Not at hc
    exact hA (by ext i j; exact hc i j)
  · rintro ⟨i, j, hij⟩ h
    exact hij (by rw [h]; rfl)

theorem isFaithful_iff {R : Type*} [Ring R] (rk : SylvesterRank R) :
    (∀ a : R, rk.rk 1 1 (oneByOne a) = 0 → a = 0) ↔
      ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), A ≠ 0 → rk.rk n m A ≠ 0 := by
  constructor
  · intro h n m A hA
    obtain ⟨i, j, hij⟩ := ne_zero_iff_exists_entry.mp hA
    -- the `1 × 1` submatrix at `(i, j)` is `oneByOne (A i j)`
    have hsub : A.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) = oneByOne (A i j) := by
      ext k l
      simp [Matrix.submatrix_apply, oneByOne]
    have hle :=
      Work.ORHughesFree.RankAPI.rk_submatrix rk (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) A
    rw [hsub] at hle
    intro hzero
    rw [hzero] at hle
    have hpos : 0 < rk.rk 1 1 (oneByOne (A i j)) :=
      lt_of_le_of_ne (rk.rk_nonneg 1 1 _) (Ne.symm (fun h0 => hij (h (A i j) h0)))
    linarith
  · intro h a ha
    have hzero : oneByOne a = 0 := by
      by_contra hne
      exact h 1 1 (oneByOne a) hne ha
    exact oneByOne_eq_zero_iff.mp hzero

end Work.ORHughesFree.Faithful
