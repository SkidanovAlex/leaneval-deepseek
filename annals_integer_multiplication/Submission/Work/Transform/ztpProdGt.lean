import Mathlib

namespace Work.Transform

/-- For `m ≥ 1`, `2 ^ (m.size - 1) ≤ m`: the value of the leading bit of `m`. -/
private lemma pow_size_le (m : ℕ) (hm : 0 < m) : 2 ^ (m.size - 1) ≤ m := by
  have hms : 0 < m.size := Nat.size_pos.mpr hm
  exact Nat.lt_size.mp (Nat.sub_lt hms (by norm_num))

/-- The product of `l` dominates `2` raised to the sum of the bit-lengths (minus one) of its
entries that are at least `2`. -/
theorem ztpProdGt (l : List ℕ) (h : ∀ t ∈ l, 0 < t) :
    2 ^ ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size - 1)).sum ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 0 < a := h a (by simp)
    have ih' : 2 ^ ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size - 1)).sum ≤ l.prod :=
      ih (fun t ht => h t (by simp [ht]))
    by_cases h2 : 2 ≤ a
    · rw [List.filter_cons_of_pos (by simpa using h2), List.map_cons, List.sum_cons, pow_add,
        List.prod_cons]
      exact Nat.mul_le_mul (pow_size_le a ha) ih'
    · rw [List.filter_cons_of_neg (by simp [h2]), List.prod_cons]
      exact le_trans ih' (Nat.le_mul_of_pos_left _ ha)

end Work.Transform
