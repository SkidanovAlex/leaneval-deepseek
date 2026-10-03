import Mathlib

universe u

namespace Work.OROneRel

/-- The `r`-th entry of the concatenation of `k` copies of `W` is `W[r % W.length]`,
provided `r` is in range. -/
theorem flatten_replicate_getElem_mod {α : Type u} {W : List α} {k r : ℕ}
    (hr : r < (List.replicate k W).flatten.length) :
    ((List.replicate k W).flatten)[r]? = W[r % W.length]? := by
  induction k generalizing r with
  | zero => exact absurd hr (by simp)
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons] at hr ⊢
    rw [List.length_append] at hr
    by_cases hi : r < W.length
    · rw [List.getElem?_append_left hi, Nat.mod_eq_of_lt hi]
    · rw [List.getElem?_append_right (le_of_not_gt hi)]
      have h' : r - W.length < (List.replicate k W).flatten.length := by omega
      rw [ih h', Nat.mod_eq_sub_mod (le_of_not_gt hi)]

end Work.OROneRel
