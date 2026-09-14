import Mathlib
import Submission.Commons.NumberTheory.Int.ncard_binary_quadratic_repr_le

namespace Commons.NumberTheory.Int

open Finset

/-- Uniform-in-`b` version of `ncard_binary_quadratic_repr_le`: for `1 ≤ b ≤ B` the
number of representations of `n` by `a * x ^ 2 + b * y ^ 2` is bounded by a single
constant times `n ^ ε`.  Since the admissible `b` form a finite set, the constants
furnished by the single-form estimate can be maximised over it. -/
theorem ncard_binary_quadratic_repr_le_bounded (a : ℕ) (ha : 1 ≤ a) (B : ℕ) (hB : 1 ≤ B)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (_ : 1 ≤ b), b ≤ B → ∀ n : ℕ, 1 ≤ n →
      (Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : ℝ)
        ≤ C * (n : ℝ) ^ eps := by
  classical
  -- For every admissible `b`, the single-form estimate provides a positive constant.
  have hex : ∀ b : ℕ, 1 ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : ℝ)
          ≤ C * (n : ℝ) ^ eps :=
    fun b hb => ncard_binary_quadratic_repr_le a b ha hb eps heps
  let cB : ℕ → ℝ := fun b => if hb : 1 ≤ b then Classical.choose (hex b hb) else 1
  have hcB_pos : ∀ b : ℕ, 1 ≤ b → 0 < cB b := by
    intro b hb
    simp only [cB, dif_pos hb]
    exact (Classical.choose_spec (hex b hb)).1
  have hcB_bound : ∀ b : ℕ, 1 ≤ b → ∀ n : ℕ, 1 ≤ n →
      (Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : ℝ)
        ≤ cB b * (n : ℝ) ^ eps := by
    intro b hb n hn
    simp only [cB, dif_pos hb]
    exact (Classical.choose_spec (hex b hb)).2 n hn
  -- Maximise over the nonempty finite set of admissible `b`.
  have hne : (Finset.Icc 1 B).Nonempty :=
    ⟨1, by rw [Finset.mem_Icc]; exact ⟨le_rfl, hB⟩⟩
  refine ⟨(Finset.Icc 1 B).sup' hne cB, ?_, ?_⟩
  · have h1mem : (1 : ℕ) ∈ Finset.Icc 1 B := by
      rw [Finset.mem_Icc]; exact ⟨le_rfl, hB⟩
    exact lt_of_lt_of_le (hcB_pos 1 le_rfl) (Finset.le_sup' cB h1mem)
  · intro b hb hbB n hn
    have hbmem : b ∈ Finset.Icc 1 B := by
      rw [Finset.mem_Icc]; exact ⟨hb, hbB⟩
    have hle : cB b ≤ (Finset.Icc 1 B).sup' hne cB := Finset.le_sup' cB hbmem
    have hpos : 0 ≤ (n : ℝ) ^ eps := Real.rpow_nonneg (by positivity) eps
    calc (Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : ℝ)
        ≤ cB b * (n : ℝ) ^ eps := hcB_bound b hb n hn
      _ ≤ (Finset.Icc 1 B).sup' hne cB * (n : ℝ) ^ eps :=
          mul_le_mul_of_nonneg_right hle hpos

end Commons.NumberTheory.Int
