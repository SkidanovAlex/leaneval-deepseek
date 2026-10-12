import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDictC.mfac_sub_single_mul` — lowering one quantum multiplies `mfac` by the occupation

The multi-index factorial `Work.BoseB4.mfac α = ∏_l (α_l)!` satisfies, for any
coordinate `k` with `α k ≠ 0`,

    `(α k : ℝ) * mfac (α - single k 1) = mfac α`.

At the coordinate `k` this is `α k · (α k - 1)! = (α k)!`, and all other factors
are unchanged because `(α - e_k) l = α l` for `l ≠ k`.

## The proof

`Work.BoseB4.mfac_add_e` gives the *raising* companion
`mfac (γ + e_l) = (γ l + 1) * mfac γ`.  Applying it with `γ = α - e_k` and
`l = k`, and using `(α - e_k) + e_k = α` (valid since `α k ≠ 0`, so
`single k 1 ≤ α`) and `((α - e_k) k : ℝ) + 1 = (α k : ℝ)`, turns it into the
statement.  The `Finsupp.single k 1` of the target is definitionally
`Work.BoseB4.e m k`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDictC

/-- **Lowering one quantum at a coordinate multiplies `mfac` by the occupation.**
If `α k ≠ 0` then `(α k) · (α - e_k)! = α!`. -/
theorem mfac_sub_single_mul {m : ℕ} (α : Fin m →₀ ℕ) (k : Fin m) (h : α k ≠ 0) :
    (α k : ℝ) * Work.BoseB4.mfac (α - Finsupp.single k 1) = Work.BoseB4.mfac α := by
  -- `e_k ≤ α`, so adding `e_k` back to `α - e_k` recovers `α`.
  have hadd : (α - Work.BoseB4.e m k) + Work.BoseB4.e m k = α := by
    rw [Work.BoseB4.e]
    exact tsub_add_cancel_of_le ((Finsupp.single_le_iff).mpr (Nat.pos_of_ne_zero h))
  -- the raising companion, at `γ = α - e_k`
  have h1 := Work.BoseB4.mfac_add_e k (α - Work.BoseB4.e m k)
  rw [hadd] at h1
  -- the occupation at `k` is `α k - 1`, so `(α k - 1) + 1 = α k`
  have h2 : (((α - Work.BoseB4.e m k) k : ℕ) : ℝ) + 1 = (α k : ℝ) := by
    have hl : (α - Work.BoseB4.e m k) k = α k - 1 := by
      rw [Finsupp.tsub_apply, Work.BoseB4.e, Finsupp.single_eq_same]
    rw [hl, Nat.cast_sub (by omega : 1 ≤ α k)]
    ring
  rw [h2] at h1
  rw [h1, Work.BoseB4.e]

end Work.BoseDictC
