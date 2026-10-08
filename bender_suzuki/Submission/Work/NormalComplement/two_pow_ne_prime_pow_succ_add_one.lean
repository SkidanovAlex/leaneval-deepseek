import Mathlib
import Submission.Work.NormalComplement.cofactor_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- An odd divisor of a power of two must be `1`. -/
private lemma odd_dvd_two_pow {m b : ℕ} (hm : Odd m) (h : m ∣ 2 ^ b) : m = 1 := by
  have hc : Nat.Coprime m (2 ^ b) := (Nat.coprime_two_right.mpr hm).pow_right b
  exact hc.eq_one_of_dvd h

/-- `2^b = m^2 + 1` has no solution for odd `m ≥ 3`: an odd square is `≡ 1 (mod 4)`, so
`m^2 + 1 ≡ 2 (mod 4)`, whereas `2^b ≡ 0 (mod 4)` once `b ≥ 2` (and `b ≤ 1` is excluded by size). -/
private lemma two_pow_ne_odd_sq_add_one (m b : ℕ) (hm : Odd m) (hm3 : 3 ≤ m) :
    2 ^ b ≠ m ^ 2 + 1 := by
  intro h
  have hm4 : (m : ZMod 4) ^ 2 = 1 := by
    obtain ⟨k, rfl⟩ := hm
    push_cast
    ring_nf
    rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4]
    ring
  have hb2 : 2 ≤ b := by
    by_contra hb
    have hb1 : b ≤ 1 := by omega
    have hle : 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) hb1
    have : m ^ 2 + 1 ≤ 2 := by rw [← h]; simpa using hle
    nlinarith [hm3]
  have hzero : (2 : ZMod 4) ^ b = 0 := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb2
    rw [pow_add]
    norm_num
    rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4]
    ring
  have hcast := congrArg (fun x : ℕ => (x : ZMod 4)) h
  push_cast at hcast
  rw [hm4, hzero] at hcast
  exact absurd hcast (by decide)

theorem two_pow_ne_prime_pow_succ_add_one (r a b : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (ha : 1 ≤ a) : 2 ^ b ≠ r ^ (a + 1) + 1 := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hr3 : 3 ≤ r := hr.odd_iff.mp hodd
  have hn2 : 2 ≤ a + 1 := by omega
  rcases Nat.even_or_odd (a + 1) with hev | hoddn
  · -- `a + 1` even: `r^(a+1)` is an odd square, so `r^(a+1) + 1 ≡ 2 (mod 4)`.
    obtain ⟨k, hk⟩ := hev
    have hk1 : 1 ≤ k := by omega
    have hrm : Odd (r ^ k) := hodd.pow
    have hrm3 : 3 ≤ r ^ k := by
      have hle : r ≤ r ^ k := by
        have := Nat.pow_le_pow_right (show 0 < r by omega) hk1
        simpa using this
      omega
    exact two_pow_ne_odd_sq_add_one (r ^ k) b hrm hrm3 (by rw [h, hk, pow_add]; ring)
  · -- `a + 1` odd: `r^(a+1) + 1 = (r+1) * C` with `C` odd and `> 1`.
    set n := a + 1
    have hdvd : (r + 1) ∣ r ^ n + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (x := r) (y := 1) hoddn
    have hCeq : (r + 1) * ((r ^ n + 1) / (r + 1)) = r ^ n + 1 := Nat.mul_div_cancel' hdvd
    have hCodd : Odd ((r ^ n + 1) / (r + 1)) := cofactor_odd r n hodd hoddn
    have hCdvd : ((r ^ n + 1) / (r + 1)) ∣ 2 ^ b := by
      refine ⟨r + 1, ?_⟩
      calc 2 ^ b = r ^ n + 1 := h
        _ = (r + 1) * ((r ^ n + 1) / (r + 1)) := hCeq.symm
        _ = ((r ^ n + 1) / (r + 1)) * (r + 1) := by ring
    have hC1 : (r ^ n + 1) / (r + 1) = 1 := odd_dvd_two_pow hCodd hCdvd
    have hrn : r ^ n = r := by
      have h2 : r + 1 = r ^ n + 1 := by
        have := hCeq
        rw [hC1, mul_one] at this
        exact this
      omega
    have hlt : r < r ^ n := by
      have h1 : r ^ 1 < r ^ n :=
        Nat.pow_lt_pow_right (show 1 < r by omega) (show 1 < n by omega)
      simpa using h1
    omega

end Work.NormalComplement
