import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring.RingNF
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_Z_mul_reindex

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-! ## Summing `f (c.natAbs ^ 2)` over a symmetric integer interval

For a function `f : ℕ → ℝ` we evaluate the sum of `f (c.natAbs ^ 2)` over the
integers `c ∈ [-x, x]`.  Every integer `d` with `1 ≤ d ≤ x` is realised as a
`natAbs` exactly twice (`c = d` and `c = -d`), while `0` is realised once, so
the sum equals `f 0 + 2 ∑_{1 ≤ d ≤ x} f (d ^ 2)`. -/

/-- Evaluation of a symmetric integer sum as a natural sum. -/
lemma sum_Icc_natAbs_sq (x : ℕ) (f : ℕ → ℝ) :
    (∑ c ∈ Finset.Icc (-(x:ℤ)) (x:ℤ), f (c.natAbs ^ 2))
      = f 0 + 2 * ∑ b ∈ Finset.Icc 1 x, f (b ^ 2) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have hIcc : Finset.Icc (-((x:ℤ) + 1)) ((x:ℤ) + 1)
        = insert (-((x:ℤ) + 1)) (insert ((x:ℤ) + 1) (Finset.Icc (-(x:ℤ)) (x:ℤ))) := by
      ext c; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [Nat.cast_succ]
    rw [hIcc]
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega)]
    rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [ih]
    rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ x + 1)]
    have hx1 : ((x:ℤ) + 1).natAbs = x + 1 := by
      rw [← Nat.cast_succ, Int.natAbs_natCast]
    simp only [Int.natAbs_neg, hx1]
    ring

/-! ## Truncating the squares by the support condition

If `G` vanishes above `x ^ (1/2)` in the sense that `x < b ^ 2 → G b = 0`, then
the sum `∑_{1 ≤ d ≤ x} G (d ^ 2)` only sees the `d` with `d ^ 4 ≤ x`, i.e.
`d ≤ √√x`. -/

/-- The square-supported sum can be truncated at `√√x`. -/
lemma sum_Icc_sq_eq_sum_Icc_sqrt (x : ℕ) (G : ℕ → ℝ)
    (hG : ∀ b : ℕ, x < b ^ 2 → G b = 0) :
    (∑ b ∈ Finset.Icc 1 x, G (b ^ 2))
      = ∑ b ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), G (b ^ 2) := by
  have hsx : Nat.sqrt (Nat.sqrt x) ≤ x :=
    le_trans (Nat.sqrt_le_self _) (Nat.sqrt_le_self _)
  have hiff : ∀ b : ℕ, b ≤ Nat.sqrt (Nat.sqrt x) ↔ b ^ 4 ≤ x := by
    intro b
    rw [Nat.le_sqrt', Nat.le_sqrt']
    ring_nf
  apply (Finset.sum_subset ?_ ?_).symm
  · intro b hb
    simp only [Finset.mem_Icc] at hb ⊢
    exact ⟨hb.1, le_trans hb.2 hsx⟩
  · intro b hb hnb
    simp only [Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1
    have hble : ¬ b ≤ Nat.sqrt (Nat.sqrt x) := by
      intro h
      exact hnb (by simp only [Finset.mem_Icc]; exact ⟨hb1, h⟩)
    have hb4 : x < b ^ 4 := by
      have : ¬ b ^ 4 ≤ x := fun h => hble ((hiff b).mpr h)
      omega
    exact hG (b ^ 2) (by rw [show (b ^ 2) ^ 2 = b ^ 4 by ring]; exact hb4)

/-- **The integer-versus-square reindexing identity.**

Summing `G (c ^ 2)` over the integers `c` with `|c| ≤ x` produces each square
`d ^ 2` (`1 ≤ d ≤ x`) with multiplicity two and `0` with multiplicity one.  The
right-hand side collects the same terms over the perfect squares `b ≤ √x`, with
`Z` the square indicator: `Z 0 = 1`, `Z (b ^ 2) = 2` for `b ≠ 0` and `Z b = 0`
otherwise.  The equality uses that `G` is supported on the squares not exceeding
`x`. -/
theorem sum_Icc_sq_eq_sum_Z (x : ℕ) (G : ℕ → ℝ) (hG : ∀ b : ℕ, x < b ^ 2 → G b = 0) :
    (∑ c ∈ Finset.Icc (-(x : ℤ)) (x : ℤ), G (c.natAbs ^ 2))
      = ∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) * G b := by
  rw [sum_Z_mul_reindex (Nat.sqrt x) G]
  rw [sum_Icc_natAbs_sq x G]
  rw [sum_Icc_sq_eq_sum_Icc_sqrt x G hG]

end Commons.NumberTheory.FriedlanderIwaniec