/-
# Vocabulary for `Work.KMTAreas.A4.amplifyDense`

The symmetric level set of the rotation `n ↦ n β` in `[-N,N]`, together with its API.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_defs

namespace Work.KMTAreas.A4

open scoped BigOperators

/-- The symmetric level set of the rotation `n ↦ n β` in the interval `[-N,N]`. -/
noncomputable def lvlS (β δ : ℝ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun n => nDist ((n : ℝ) * β) ≤ δ)

theorem mem_lvlS {β δ : ℝ} {N : ℕ} {n : ℤ} :
    n ∈ lvlS β δ N ↔ -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) ∧ nDist ((n : ℝ) * β) ≤ δ := by
  simp [lvlS, and_assoc]

/-- `nDist` is at most the distance to any integer, for a multiple of `β`. -/
theorem nDist_mul_le_abs {β : ℝ} {δ : ℝ} {n : ℤ}
    (h : ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ) :
    nDist ((n : ℝ) * β) ≤ δ := by
  obtain ⟨m, hm⟩ := h
  have h1 : nDist ((n : ℝ) * β) = nDist (β * (n : ℝ)) := by rw [mul_comm]
  rw [h1]
  exact (nDist_le_abs_sub_int (β * (n : ℝ)) m).trans hm

/-- With `a = round (q β)`, the error `|β - a/q|` equals `nDist (q β)/q`. -/
theorem abs_sub_div_round {β : ℝ} {q : ℕ} (hq : 1 ≤ q) :
    |β - ((round ((q : ℝ) * β) : ℤ) : ℝ) / (q : ℝ)| = nDist ((q : ℝ) * β) / (q : ℝ) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h : β - ((round ((q : ℝ) * β) : ℤ) : ℝ) / (q : ℝ)
      = (β * (q : ℝ) - ((round ((q : ℝ) * β) : ℤ) : ℝ)) / (q : ℝ) := by
    field_simp
  rw [h, abs_div, abs_of_pos hqpos, mul_comm β (q : ℝ), nDist]

end Work.KMTAreas.A4
