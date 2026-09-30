import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Real

theorem dyadic_between {a : ℝ} (ha : 1 < a) :
    ∃ n : ℕ, (2 : ℝ) ^ n < a ∧ a ≤ (2 : ℝ) ^ (n + 1) := by
  classical
  let p : ℕ → Prop := fun k => a ≤ (2 : ℝ) ^ (k + 1)
  have hp : ∃ k, p k := by
    rcases exists_nat_gt a with ⟨m, ham⟩
    refine ⟨m, ?_⟩
    have hm_lt : (m : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast (Nat.lt_two_pow_self (n := m))
    have ha2m : a < (2 : ℝ) ^ m := lt_trans ham hm_lt
    have hmono : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ m)
    exact le_trans (le_of_lt ha2m) hmono
  refine ⟨Nat.find hp, ?_, ?_⟩
  · -- show (2 : ℝ) ^ Nat.find hp < a
    by_cases hn0 : Nat.find hp = 0
    · rw [hn0]
      norm_num
      exact ha
    · have hnpos : 0 < Nat.find hp := Nat.pos_of_ne_zero hn0
      have hle_false : ¬ a ≤ (2 : ℝ) ^ Nat.find hp := by
        intro hle
        have hpn1 : p (Nat.find hp - 1) := by
          unfold p
          simpa [Nat.sub_add_cancel hnpos] using hle
        have hn_gt : Nat.find hp - 1 < Nat.find hp := Nat.sub_one_lt hn0
        exact (Nat.find_min hp hn_gt) hpn1
      exact lt_of_not_ge hle_false
  · exact Nat.find_spec hp

end Commons.Analysis.Real