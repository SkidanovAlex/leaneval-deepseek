import Mathlib

namespace Work.Zassenhaus

theorem zass_coprime_pow_half {p k : ℕ} (hp : Nat.Prime p) (hpodd : Odd p) (hk : 1 ≤ k) :
    Nat.Coprime (p ^ k) ((p ^ k - 1) / 2) := by
  have hm : Odd (p ^ k) := hpodd.pow
  obtain ⟨q, hq⟩ : ∃ q, p ^ k = 2 * q + 1 := hm
  have hhalf : (p ^ k - 1) / 2 = q := by omega
  rw [hhalf, Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  have h1 : (p ^ k).gcd q ∣ p ^ k := Nat.gcd_dvd_left _ _
  have h2 : (p ^ k).gcd q ∣ q := Nat.gcd_dvd_right _ _
  have h3 : (p ^ k).gcd q ∣ 2 * q := dvd_mul_of_dvd_right h2 2
  have h4 : (p ^ k).gcd q ∣ p ^ k - 2 * q := Nat.dvd_sub h1 h3
  have h5 : p ^ k - 2 * q = 1 := by omega
  rwa [h5] at h4

end Work.Zassenhaus
