import Mathlib
import Submission.Work.OROneRel.bandWinDefs
import Submission.Work.OROneRel.band_hnnConjMap_injective

namespace Work.OROneRel

theorem winE_succ_union (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) (e : Fin 2 × ℤ) :
    e ∈ winE (tlW p q) 0 (m + 1) ↔
      e ∈ winE (tlW p q) 0 m ∨ e = ((0 : Fin 2), m + 1 - (q : ℤ)) ∨
        e = ((1 : Fin 2), m + 1) := by
  -- Write `e = (x, i)` and split on the two letters `x = 0` (`a`) and `x = 1` (`b`).
  obtain ⟨x, i⟩ := e
  fin_cases x <;>
    -- `winE (tlW p q) 0 M` unfolds to the four level bounds; for the letter `0` the weight is
    -- `q`, for the letter `1` it is `-p`.
    rw [mem_winE, mem_winE] <;>
    simp only [tlW, Fin.isValue, Prod.mk.injEq] <;>
    -- What is new in the window `[0, m+1]` compared with `[0, m]` is the single edge
    -- `((0 : Fin 2), m + 1 - q)` (letter `0`, from the level equation `i + q = m + 1`) resp.
    -- `((1 : Fin 2), m + 1)` (letter `1`, from `i = m + 1`); the hypothesis `hm1` supplies the
    -- lower bounds for these two edges.  All that is left is integer arithmetic.
    omega

end Work.OROneRel
