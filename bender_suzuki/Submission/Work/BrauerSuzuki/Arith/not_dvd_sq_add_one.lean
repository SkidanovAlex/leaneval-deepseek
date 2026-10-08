import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Arith

/-- For `n ≥ 2`, `4 = 2 ^ 2` divides `2 ^ n`. -/
lemma four_dvd_two_pow (n : ℕ) (hn : 2 ≤ n) : 4 ∣ 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add]
  norm_num

/-- No natural number `t` has `4 ∣ t ^ 2 + 1`: modulo `4`, a square is `0` or `1`,
so `t ^ 2 + 1` is never `0`. -/
lemma not_four_dvd_sq_add_one (t : ℕ) : ¬ (4 ∣ t ^ 2 + 1) := by
  intro h4
  -- Reduce the divisibility to an identity in `ZMod 4`.
  have hcast : ((t ^ 2 + 1 : ℕ) : ZMod 4) = 0 := by
    obtain ⟨k, hk⟩ := h4
    rw [hk]
    push_cast
    rw [show (4 : ZMod 4) = 0 by decide, zero_mul]
  -- In `ZMod 4`, `x ^ 2 + 1 ≠ 0` for every `x`.
  have hkey : ∀ x : ZMod 4, x ^ 2 + 1 ≠ 0 := by decide
  have h2 : ((t : ZMod 4)) ^ 2 + 1 = 0 := by
    have := hcast
    push_cast at this
    simpa using this
  exact hkey (t : ZMod 4) h2

theorem not_dvd_sq_add_one (t n : ℕ) (hn : 3 ≤ n) : ¬ (2 ^ n ∣ t ^ 2 + 1) := by
  intro h
  have hn2 : 2 ≤ n := by omega
  -- `4 ∣ 2 ^ n`, so `4 ∣ t ^ 2 + 1` would follow.
  exact not_four_dvd_sq_add_one t (dvd_trans (four_dvd_two_pow n hn2) h)

end Work.BrauerSuzuki.Arith
