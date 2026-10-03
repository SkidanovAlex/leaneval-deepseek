import Mathlib

/-!
# Vocabulary for the "dense multiples" arithmetic step of Area A4
-/

set_option autoImplicit false

namespace Work.KMTAreas.A4

/-- The distance from `x` to the nearest integer. -/
noncomputable def nDist (x : ℝ) : ℝ := |x - round x|

theorem nDist_nonneg (x : ℝ) : 0 ≤ nDist x := abs_nonneg _

theorem nDist_le_half (x : ℝ) : nDist x ≤ 1 / 2 := by
  rw [nDist]; exact abs_sub_round x

/-- `nDist` is at most the distance to any integer. -/
theorem nDist_le_abs_sub_int (x : ℝ) (m : ℤ) : nDist x ≤ |x - (m : ℝ)| := by
  rw [nDist]; exact round_le x m

/-- `nDist` is invariant under integer translations. -/
theorem nDist_add_int (x : ℝ) (m : ℤ) : nDist (x + (m : ℝ)) = nDist x := by
  rw [nDist, nDist, round_add_intCast]
  congr 1
  push_cast
  ring

theorem nDist_sub_int (x : ℝ) (m : ℤ) : nDist (x - (m : ℝ)) = nDist x := by
  have h := nDist_add_int (x - (m:ℝ)) m
  rw [sub_add_cancel] at h; exact h.symm

theorem nDist_neg (x : ℝ) : nDist (-x) = nDist x := by
  have h1 : nDist (-x) ≤ nDist x := by
    rw [nDist]
    have h := round_le (-x) (-(round x))
    have he : (-x) - ((-(round x) : ℤ) : ℝ) = -(x - (round x : ℝ)) := by push_cast; ring
    rw [he, abs_neg] at h
    exact h
  have h2 : nDist x ≤ nDist (-x) := by
    rw [nDist]
    have h := round_le x (-(round (-x)))
    have he : x - ((-(round (-x)) : ℤ) : ℝ) = -((-x) - (round (-x) : ℝ)) := by push_cast; ring
    rw [he, abs_neg] at h
    exact h
  linarith

/-- The predicate "`β n` is within `δ` of an integer". -/
def goodBy (β δ : ℝ) (n : ℕ) : Prop := ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ

theorem goodBy_iff_nDist_le (β δ : ℝ) (n : ℕ) : goodBy β δ n ↔ nDist (β * n) ≤ δ := by
  constructor
  · rintro ⟨m, hm⟩
    exact (nDist_le_abs_sub_int (β * n) m).trans hm
  · intro h
    refine ⟨round (β * n), ?_⟩
    have h1 : nDist (β * n) = |β * n - (round (β * n) : ℝ)| := rfl
    rwa [h1] at h

/-- The level set: the `n ∈ [1,N]` with `nDist (n β) ≤ δ`. -/
noncomputable def lvl (β δ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => nDist ((n : ℝ) * β) ≤ δ)

theorem mem_lvl {β δ : ℝ} {N n : ℕ} :
    n ∈ lvl β δ N ↔ 1 ≤ n ∧ n ≤ N ∧ nDist ((n : ℝ) * β) ≤ δ := by
  simp [lvl, and_assoc]

end Work.KMTAreas.A4
