import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem finitePlace_basic {K : Type*} [Field K] [NumberField K] (w : NumberField.FinitePlace K) :
    0 < w 2 ∧ w 2 ≤ 1 ∧ (∀ x : K, 0 ≤ w x) ∧ (∀ N : ℕ, w ((N : ℕ) : K) ≤ 1) ∧
      (∀ N : ℤ, w ((N : ℤ) : K) ≤ 1) := by
  -- Non-archimedean induction: natural numbers have place value at most one.
  have hnat : ∀ N : ℕ, w ((N : ℕ) : K) ≤ 1 := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      calc w ((n : K) + 1) ≤ max (w (n : K)) (w (1 : K)) := map_add_le_max w _ _
        _ ≤ 1 := by simp [ih]
  have hint : ∀ N : ℤ, w ((N : ℤ) : K) ≤ 1 := by
    intro N
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
    · simpa using hnat n
    · rw [Int.cast_neg, Int.cast_natCast, map_neg_eq_map]
      exact hnat n
  refine ⟨?_, ?_, ?_, hnat, hint⟩
  · rw [NumberField.FinitePlace.pos_iff]; norm_num
  · simpa using hnat 2
  · exact fun x => apply_nonneg w x

end Work.BW
