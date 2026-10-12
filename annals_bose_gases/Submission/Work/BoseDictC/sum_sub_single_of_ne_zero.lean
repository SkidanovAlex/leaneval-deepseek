import Mathlib.Data.Finsupp.Order
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseDictC

/-- Subtracting the basis vector `e k` from `α : Fin m →₀ ℕ` when `α k ≠ 0` drops the
total mode occupation (`∑ j, α j`) by exactly one.  The pointwise description of the
Finsupp truncated subtraction (`Finsupp.tsub_apply`) identifies `α - single k 1` with
`α.update k (α k - 1)`, and `Finsupp.sum_update_add` computes the sum of an update. -/
theorem sum_sub_single_of_ne_zero {m : ℕ} (α : Fin m →₀ ℕ) (k : Fin m) (h : α k ≠ 0) :
    (α - Finsupp.single k 1).sum (fun _ j => j) = α.sum (fun _ j => j) - 1 := by
  have hk : 0 < α k := Nat.pos_of_ne_zero h
  have hsub : α - Finsupp.single k 1 = α.update k (α k - 1) := by
    ext j
    rw [Finsupp.tsub_apply, Finsupp.update_apply]
    by_cases hj : j = k
    · subst hj; simp
    · rw [Finsupp.single_eq_of_ne hj]; simp [hj]
  rw [hsub]
  have hsu : (α.update k (α k - 1)).sum (fun _ j => j) + α k
      = α.sum (fun _ j => j) + (α k - 1) := by
    have := Finsupp.sum_update_add α k (α k - 1) (fun _ j => j)
      (by intro i; rfl) (by intro i a b; rfl)
    simpa using this
  omega

end Work.BoseDictC
