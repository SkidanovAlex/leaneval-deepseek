import Submission.Work.Deep.GKO.NarrowImports

/-!
# The degree sequence obtained by deleting one edge

Helper module for the deficiency-matching decomposition
(`Work.Deep.GKO.exists_deficiencyMatchings`): `decrementTwo d u w` is the degree
sequence obtained from `d` by deleting a single edge joining the (distinct)
vertices `u` and `w`, i.e. the degrees of `u` and of `w` are lowered by one and
all other degrees are unchanged.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.GKO

/-- The degree sequence obtained from `d` by removing one edge joining `u` and `w`
(the degrees of `u` and of `w` are lowered by one; all other degrees are unchanged). -/
def decrementTwo {n : ℕ} (d : Fin n → ℕ) (u w : Fin n) : Fin n → ℕ :=
  fun v => d v - (if v = u ∨ v = w then 1 else 0)

@[simp]
theorem decrementTwo_eq_left {n : ℕ} (d : Fin n → ℕ) (u w : Fin n) :
    decrementTwo d u w u = d u - 1 := by
  simp [decrementTwo]

@[simp]
theorem decrementTwo_eq_right {n : ℕ} (d : Fin n → ℕ) (u w : Fin n) :
    decrementTwo d u w w = d w - 1 := by
  simp [decrementTwo]

theorem decrementTwo_of_ne {n : ℕ} (d : Fin n → ℕ) {u w v : Fin n}
    (hvu : v ≠ u) (hvw : v ≠ w) : decrementTwo d u w v = d v := by
  simp [decrementTwo, hvu, hvw]

theorem decrementTwo_le {n : ℕ} (d : Fin n → ℕ) (u w v : Fin n) :
    decrementTwo d u w v ≤ d v := by
  by_cases h : v = u ∨ v = w <;> simp [decrementTwo, h]

end Work.Deep.GKO
