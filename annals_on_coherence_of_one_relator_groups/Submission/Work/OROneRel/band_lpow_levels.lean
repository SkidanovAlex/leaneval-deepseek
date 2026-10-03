import Mathlib
import Submission.Work.OROneRel.bandLoopsDefs

/-!
# The levels of a power of a word in the band

If the walk of `T` (started at level `0`) stays inside the window `[0,L]` and has total weight
`lsig c T = 1` (one step upwards per copy), then the `n`-fold concatenation `lpow T n` has all its
levels in `[0, n + L]`: each of the `n` copies starts at level `k ≤ n - 1` and adds a value between
`0` and `L`, so the maximal level is `(n-1) + L ≤ n + L`, while the lower bound `0` needs no
correction at all because every level reached inside a copy is `≥` the level at which the copy
starts, and the copies start at `0, 1, …, n-1`.

The two bounds are proved separately by induction on `n`, using the additivity lemmas
`levLe_append` / `levGe_append` (with `lsig c T = 1` supplying the shift of the level between two
consecutive copies) and the monotonicity lemmas `levLe_mono` / `levGe_mono` of
`Submission.Work.OROneRel.bandLoopsDefs`.
-/

namespace Work.OROneRel

universe u

/-- **The levels of `lpow T n` are in `[0, n + L]`** when the walk of `T` stays in the window
`[0,L]` and `lsig c T = 1`. -/
theorem band_lpow_levels {α : Type u} {c : α → ℤ} {T : List (α × Bool)} {L : ℤ} (h : band c 0 L T)
    (h1 : lsig c T = 1) (n : ℕ) :
    levLe c (n + L) (lpow T n) ∧ levGe c 0 (lpow T n) := by
  have hlevLe : levLe c L T := fun k hk => (h k hk).2
  have hlevGe : levGe c 0 T := fun k hk => (h k hk).1
  have h0L : (0 : ℤ) ≤ L := (h.zero).2
  constructor
  · -- upper bound: copy `m` starts at level `m`, so it ends at most at `m + L ≤ (m+1) + L`
    induction n with
    | zero =>
      rw [lpow_zero]
      exact levLe_nil.mpr (by simpa using h0L)
    | succ m ih =>
      rw [lpow_succ]
      have hA : levLe c ((m : ℤ) + 1 + L) T := levLe_mono hlevLe (by linarith)
      have hB : levLe c ((m : ℤ) + 1 + L - lsig c T) (lpow T m) := by
        have heq : (m : ℤ) + 1 + L - lsig c T = (m : ℤ) + L := by rw [h1]; ring
        rw [heq]; exact ih
      have hres := levLe_append hA hB
      simpa [Nat.cast_add, Nat.cast_one] using hres
  · -- lower bound: within a copy the level never drops below the level at which it started
    induction n with
    | zero =>
      rw [lpow_zero]
      exact levGe_nil.mpr (by norm_num)
    | succ m ih =>
      rw [lpow_succ]
      have hB : levGe c (0 - lsig c T) (lpow T m) := by
        have heq : (0 : ℤ) - lsig c T = -1 := by rw [h1]; ring
        rw [heq]
        exact levGe_mono ih (by norm_num)
      exact levGe_append hlevGe hB

end Work.OROneRel
