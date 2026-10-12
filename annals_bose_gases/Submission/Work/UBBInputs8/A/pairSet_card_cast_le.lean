import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

/-- The number of ordered pairs of distinct coordinates, `#(pairSet N)`, is at most `N ^ 2`:
`pairSet N` is the set of all ordered pairs `(i, j)` with `i ≠ j`, a subset of the full
set `Fin N × Fin N` of cardinality `N * N`. -/
theorem pairSet_card_cast_le (N : ℕ) :
    ((Submission.BoseGases.pairSet N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h1 : (Submission.BoseGases.pairSet N).card ≤ N * N := by
    calc (Submission.BoseGases.pairSet N).card
        ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
      _ = N * N := by simp [Finset.card_univ, Fintype.card_prod]
  have h2 : ((N * N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  calc ((Submission.BoseGases.pairSet N).card : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (N : ℝ) ^ 2 := h2

end Work.UBBInputs8.A
