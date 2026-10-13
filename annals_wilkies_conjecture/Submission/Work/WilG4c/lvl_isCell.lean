import Mathlib
import Submission.Work.WilG4c.CellParamDefs
import Submission.Work.WilE8.Sharp.CellTransport

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open WilkiesDesign

/-- Auxiliary downward induction: below the top level, the level-`m` set of a cell is obtained
from the level-`(m+1)` set by dropping the last coordinate, and `projLast` of a cell is a cell. -/
theorem lvl_isCell_aux (p N : ℕ) {κ : Set (Fin (p+N) → ℝ)} (h : WilkiesDesign.IsCell (p+N) κ) :
    ∀ k m, m ≤ N → N - m ≤ k → WilkiesDesign.IsCell (p+m) (Work.WilG4c.lvl p N κ m) := by
  intro k
  induction k with
  | zero =>
      intro m hm hk
      have hmN : m = N := by omega
      subst hmN
      rw [Work.WilG4c.lvl_self κ]
      exact h
  | succ k ih =>
      intro m hm hk
      by_cases hmN : m = N
      · subst hmN
        rw [Work.WilG4c.lvl_self κ]
        exact h
      · have hmlt : m < N := lt_of_le_of_ne hm hmN
        have hN1 : N - (m+1) ≤ k := by omega
        have hstep : WilkiesDesign.IsCell (p+(m+1)) (Work.WilG4c.lvl p N κ (m+1)) :=
          ih (m+1) (by omega) hN1
        rw [Work.WilG4c.lvl_succ κ hmlt]
        exact Work.WilE8.Sharp.isCell_projLast hstep

theorem lvl_isCell (p N : ℕ) {κ : Set (Fin (p+N) → ℝ)} (h : WilkiesDesign.IsCell (p+N) κ) :
    ∀ m, m ≤ N → WilkiesDesign.IsCell (p+m) (Work.WilG4c.lvl p N κ m) := by
  intro m hm
  exact lvl_isCell_aux p N h (N - m) m hm (le_refl _)

end Work.WilG4c
