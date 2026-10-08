import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

theorem pow_eq_pow_of_orderOf_eq_two {G : Type*} [Group G] {g : G} {n : ℕ} (hn : 1 ≤ n)
    (hg : orderOf g = 2 ^ n) {k : ℕ} (hk : orderOf (g ^ k) = 2) :
    g ^ k = g ^ (2 ^ (n - 1)) := by
  -- `2 ^ n = 2 ^ (n - 1) * 2` since `n ≥ 1`.
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    have h : 2 ^ n = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
    rw [h, pow_succ]
  -- `(g ^ k) ^ 2 = 1`
  have hk2 : g ^ (k * 2) = 1 := by
    have h2 : (g ^ k) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g ^ k)
      rwa [hk] at this
    rw [pow_mul]; exact h2
  -- hence `2 ^ n ∣ 2 * k`
  have hdvd : 2 ^ n ∣ k * 2 := by
    rw [← hg]
    exact orderOf_dvd_iff_pow_eq_one.mpr hk2
  -- but `2 ^ n ∤ k`, since `g ^ k ≠ 1`
  have hndvd : ¬ 2 ^ n ∣ k := by
    intro hcon
    rw [← hg] at hcon
    have h1 : g ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hcon
    have h2' : orderOf (g ^ k) = 1 := by rw [h1, orderOf_one]
    omega
  -- therefore `2 ^ (n - 1) ∣ k`
  have hdvd1 : 2 ^ (n - 1) ∣ k := by
    have h := hdvd
    rw [hpow] at h
    rwa [Nat.mul_dvd_mul_iff_right (by norm_num : 0 < 2)] at h
  -- write `k = 2 ^ (n - 1) * t`, then `t` is odd, so `k ≡ 2 ^ (n - 1) [MOD 2 ^ n]`
  have hmod : k ≡ 2 ^ (n - 1) [MOD 2 ^ n] := by
    obtain ⟨t, rfl⟩ := hdvd1
    have h2t : ¬ 2 ∣ t := by
      intro h
      apply hndvd
      rw [hpow, Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : (0 : ℕ) < 2) (n - 1))]
      exact h
    obtain ⟨s, hs⟩ := Nat.not_even_iff_odd.mp (fun hE => h2t (even_iff_two_dvd.mp hE))
    rw [hs, Nat.ModEq]
    have hkey : 2 ^ (n - 1) * (2 * s + 1) = 2 ^ n * s + 2 ^ (n - 1) := by
      have h : 2 ^ n = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
      rw [h, pow_succ]
      ring
    rw [hkey, Nat.mul_add_mod_self_left]
  rw [pow_eq_pow_iff_modEq]
  rwa [hg]

end Work.BrauerSuzuki.Quaternion
