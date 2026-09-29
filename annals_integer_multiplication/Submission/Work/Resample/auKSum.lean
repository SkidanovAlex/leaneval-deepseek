import Mathlib
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auKArith

/-!
# The window centre is the telescoping sum of its increments

The resampling word emits, for each output index `k`, the slide `auK s t (k+1) - auK s t k` of the
window centre (`auSizes`, `auK_step_sub`).  Here we record that these slides telescope: the sum of
the first `k` of them is the `k`-th centre itself.

Because `auK s t` is monotone in `k` (`auKArith_mono`) the `ℕ`-subtractions do not truncate, and the
telescoping identity reduces to `f k - f 0` with `f 0 = 0` (`auK_zero`).
-/

namespace Work.Resample

/-- The window centre of the zeroth output is `0`, with no hypothesis on `t` (the degenerate case
`t = 0` makes the defining quotient `0/0 = 0`). -/
lemma auK_zero_all (s t : ℕ) : auK s t 0 = 0 := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp [auK]
  · exact auK_zero h

/-- Telescoping of a monotone `ℕ`-valued sequence: `∑_{j<k} (f (j+1) - f j) = f k - f 0`.
Monotonicity is what makes the truncated `ℕ`-subtractions add up. -/
lemma list_sum_range_sub_of_mono (f : ℕ → ℕ) (hf : Monotone f) (k : ℕ) :
    ((List.range k).map (fun j => f (j + 1) - f j)).sum = f k - f 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have h1 : f n ≤ f (n + 1) := hf (Nat.le_succ n)
    have h2 : f 0 ≤ f n := hf (Nat.zero_le n)
    simp only [List.map_singleton, List.sum_singleton]
    omega

theorem auKSum (s t k : ℕ) :
    ((List.range k).map (fun j => Work.Resample.auK s t (j+1) - Work.Resample.auK s t j)).sum
      = Work.Resample.auK s t k := by
  rw [list_sum_range_sub_of_mono (auK s t) (auKArith_mono s t) k, auK_zero_all s t, Nat.sub_zero]

end Work.Resample
