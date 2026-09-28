import Mathlib

namespace Work.HP.HP2

/-- If every prime `p ≤ w` divides `P`, and `k ≥ 2` is coprime to `P`,
then `w < k`. Indeed, any prime divisor `p` of `k` satisfies `p ≤ k ≤ w`
hence `p ∣ P`, contradicting coprimality. -/
theorem rough_gt_w (w : ℝ) (P : ℕ) (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ P)
    {k : ℕ} (hk : 2 ≤ k) (hcop : Nat.Coprime k P) : w < (k : ℝ) := by
  by_contra h
  -- `h : ¬ w < k`, so `k ≤ w`
  have hkw : (k : ℝ) ≤ w := not_lt.mp h
  -- a prime divisor of `k` exists since `k ≠ 1`
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  have hplek : p ≤ k := Nat.le_of_dvd (by omega) hpk
  have hpw : (p : ℝ) ≤ w := le_trans (by exact_mod_cast hplek) hkw
  have hpP : p ∣ P := hP p hp hpw
  -- then `p` divides both `k` and `P`, so it divides their gcd, which is `1`
  have hpg : p ∣ Nat.gcd k P := Nat.dvd_gcd hpk hpP
  have hg : Nat.gcd k P = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  rw [hg] at hpg
  exact hp.not_dvd_one hpg

end Work.HP.HP2
