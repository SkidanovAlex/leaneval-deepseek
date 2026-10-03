import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Pow

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-! ## The square-indicator reindexing identity

We prove that for any `f : ℕ → ℝ`,
`∑_{b ≤ r} Z(b) f b = f 0 + 2 ∑_{1 ≤ c ≤ √r} f (c²)`,
where `Z` is the square indicator `Z(0) = 1`, `Z(b²) = 2` for `b ≠ 0`,
and `Z(b) = 0` otherwise.

We mimic the combinatorial core of the (already proven) `ℕ`-valued version
`MdNum_reindex_squares`: split off the `b = 0` term, then reindex the nonzero
perfect squares by their square roots. -/

/-- Splitting off the `b = 0` term from a sum over `range (r + 1)`. -/
private lemma fi_sum_range_split (f : ℕ → ℝ) (r : ℕ) :
    (∑ b ∈ Finset.range (r + 1),
        (if b = 0 then (1:ℝ) else if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = f 0 + ∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b := by
  rw [Finset.sum_range_succ']
  have hI : Finset.Ico 1 (r + 1) = Finset.Icc 1 r := by
    ext b; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hg0 : (if (0:ℕ) = 0 then (1:ℝ) else if Nat.sqrt 0 ^ 2 = 0 then 2 else 0) * f 0
      = f 0 := by
    simp
  have hsum : (∑ k ∈ Finset.range r,
        (if k + 1 = 0 then (1:ℝ) else if Nat.sqrt (k + 1) ^ 2 = k + 1 then 2 else 0)
          * f (k + 1))
      = ∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b := by
    rw [← hI, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_neg (by omega : ¬ (k + 1 = 0)), Nat.add_comm 1 k]
  rw [hsum, hg0, add_comm]

/-- Reindexing the square terms of `[1, r]` by their square roots. -/
private lemma fi_sum_squares (f : ℕ → ℝ) (r : ℕ) :
    (∑ b ∈ (Finset.Icc 1 r).filter (fun b => Nat.sqrt b ^ 2 = b), f b)
      = ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  have hF : (Finset.Icc 1 r).filter (fun b => Nat.sqrt b ^ 2 = b)
      = (Finset.Icc 1 (Nat.sqrt r)).image (fun c => c ^ 2) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hb1, hbr⟩, hbsq⟩
      exact ⟨Nat.sqrt b, ⟨by rw [Nat.le_sqrt']; omega,
        by rw [Nat.le_sqrt']; rw [hbsq]; exact hbr⟩, hbsq⟩
    · rintro ⟨c, ⟨hc1, hcr⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · calc 1 = 1 ^ 2 := by norm_num
          _ ≤ c ^ 2 := Nat.pow_le_pow_left hc1 2
      · exact Nat.le_sqrt'.mp hcr
      · rw [Nat.sqrt_eq']
  rw [hF]
  exact Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)

/-- Reindexing the weighted sum over `[1, r]` using the square-root bijection. -/
private lemma fi_sum_weight (f : ℕ → ℝ) (r : ℕ) :
    (∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = 2 * ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  have h1 : ∀ b ∈ Finset.Icc 1 r,
      (if Nat.sqrt b ^ 2 = b then (2:ℝ) else 0) * f b
        = 2 * (if Nat.sqrt b ^ 2 = b then f b else 0) := by
    intro b _
    by_cases h : Nat.sqrt b ^ 2 = b <;> simp [h]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_filter,
    fi_sum_squares f r]

theorem sum_Z_mul_reindex (r : ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.range (r + 1),
        (if b = 0 then (1:ℝ) else if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = f 0 + 2 * ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  rw [fi_sum_range_split f r, fi_sum_weight f r]

end Commons.NumberTheory.FriedlanderIwaniec