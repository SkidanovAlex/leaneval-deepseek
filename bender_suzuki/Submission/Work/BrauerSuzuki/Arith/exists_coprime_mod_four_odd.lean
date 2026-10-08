import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Arith

/-- For odd `m` there is `k` with `k % 4 = 1`, `k % m = m - 1` and `k` coprime to `4 * m`
(explicit witness: `k = 2 * m ^ 2 - 1`, for which `2 * m ^ 2 - 1 ≡ 1 [MOD 4]` and
`2 * m ^ 2 - 1 ≡ -1 [MOD m]`). -/
theorem exists_coprime_mod_four_odd {m : ℕ} (hm : Odd m) :
    ∃ k : ℕ, k % 4 = 1 ∧ k % m = m - 1 ∧ k.Coprime (4 * m) := by
  obtain ⟨t, ht⟩ := hm
  have hm1 : 1 ≤ m := by omega
  -- the explicit witness `k = 2 * m ^ 2 - 1`, written in the form `4 * s + 1`
  have hk : 2 * m ^ 2 - 1 = 4 * (2 * t ^ 2 + 2 * t) + 1 := by
    have h : 2 * m ^ 2 = 4 * (2 * t ^ 2 + 2 * t) + 2 := by rw [ht]; ring
    omega
  refine ⟨2 * m ^ 2 - 1, ?_, ?_, ?_⟩
  · -- `k % 4 = 1`
    rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (by norm_num : 1 < 4)]
  · -- `k % m = m - 1`: both `2 * m ^ 2` and `m` vanish mod `m`
    have hA : 2 * m ^ 2 ≡ m [MOD m] := by
      show 2 * m ^ 2 % m = m % m
      rw [show 2 * m ^ 2 = m * (2 * m) by ring, Nat.mul_mod_right, Nat.mod_self]
    have hB : 2 * m ^ 2 - 1 ≡ m - 1 [MOD m] :=
      Nat.ModEq.sub (show 0 < 2 * m ^ 2 by positivity) hm1 hA (Nat.ModEq.refl 1)
    have hB' : (2 * m ^ 2 - 1) % m = (m - 1) % m := hB
    rw [hB', Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  · -- coprimality
    have hodd : Odd (2 * m ^ 2 - 1) := ⟨2 * (2 * t ^ 2 + 2 * t), by omega⟩
    have h4 : (2 * m ^ 2 - 1).Coprime 4 := by
      have := (Nat.coprime_two_right.mpr hodd).pow_right 2
      simpa using this
    have hcm : (m - 1).Coprime m := by
      rw [Nat.coprime_self_sub_left hm1]
      exact Nat.coprime_one_left m
    have h1 : m * (2 * m - 1) + m = 2 * m ^ 2 := by
      have h : m * (2 * m - 1) + m = m * ((2 * m - 1) + 1) := by ring
      rw [h, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]
      ring
    have hk2 : 2 * m ^ 2 - 1 = m * (2 * m - 1) + (m - 1) := by omega
    have hcx : (2 * m ^ 2 - 1).Coprime m := by
      rw [hk2, Nat.coprime_mul_left_add_left]
      exact hcm
    exact h4.mul_right hcx

end Work.BrauerSuzuki.Arith
