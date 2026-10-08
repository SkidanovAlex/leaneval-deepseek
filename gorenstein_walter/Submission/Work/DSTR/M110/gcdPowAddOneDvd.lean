import Mathlib

namespace Work.DSTR.M110

/-- Arithmetic core: if `g ∣ A^2 - 1` and `g ∣ A^b + 1` with `b` odd, then `g ∣ A + 1`.
Indeed modulo `g` we have `A^2 ≡ 1`, so `A^b ≡ A` (as `b = 2t+1`), and `A^b + 1 ≡ 0`
forces `A ≡ -1`. -/
private lemma dvd_succ_of_dvd_sq_sub_one_of_dvd_pow_add_one {A b g : ℕ} (hb : Odd b)
    (h1 : g ∣ A ^ 2 - 1) (h2 : g ∣ A ^ b + 1) : g ∣ A + 1 := by
  obtain ⟨t, ht⟩ := hb
  subst ht
  -- `A^2 - 1` divides `A^(2*t) - 1`
  have h3 : A ^ 2 - 1 ∣ A ^ (2 * t) - 1 := by
    rw [pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (A ^ 2) t
  have hg3 : g ∣ A ^ (2 * t) - 1 := h1.trans h3
  -- `A * (A^(2*t) - 1) = A^(2*t+1) - A`
  have h4 : A * (A ^ (2 * t) - 1) = A ^ (2 * t + 1) - A := by
    rw [Nat.mul_sub_left_distrib, mul_comm A (A ^ (2 * t)), ← pow_succ, mul_one]
  have h5 : g ∣ A ^ (2 * t + 1) - A := by
    rw [← h4]
    exact dvd_mul_of_dvd_right hg3 A
  have h6 : g ∣ (A ^ (2 * t + 1) + 1) - (A ^ (2 * t + 1) - A) := Nat.dvd_sub h2 h5
  have h7 : (A ^ (2 * t + 1) + 1) - (A ^ (2 * t + 1) - A) = A + 1 := by
    have hle : A ≤ A ^ (2 * t + 1) := Nat.le_self_pow (by omega) A
    omega
  rwa [h7] at h6

/-- `(A^b+1) ∣ A^(2*b) - 1` for every `b`. -/
private lemma pow_add_one_dvd_pow_two_mul_sub_one (A b : ℕ) : (A ^ b + 1) ∣ A ^ (2 * b) - 1 := by
  have h2 : A ^ (2 * b) = (A ^ b) ^ 2 := by rw [mul_comm 2 b, pow_mul]
  rw [h2]
  have hsq : (A ^ b) ^ 2 - 1 = (A ^ b + 1) * (A ^ b - 1) := by
    simpa using Nat.sq_sub_sq (A ^ b) 1
  rw [hsq]
  exact dvd_mul_right _ _

/-- `A^a - 1` divides `A^(2*a) - 1`. -/
private lemma pow_sub_one_dvd_pow_two_mul_sub_one (A a : ℕ) : (A ^ a - 1) ∣ A ^ (2 * a) - 1 := by
  have h2 : A ^ (2 * a) = (A ^ a) ^ 2 := by rw [mul_comm 2 a, pow_mul]
  rw [h2]
  have hsq : (A ^ a) ^ 2 - 1 = (A ^ a + 1) * (A ^ a - 1) := by
    simpa using Nat.sq_sub_sq (A ^ a) 1
  rw [hsq]
  exact dvd_mul_left _ _

/-- `A^a + 1` divides `A^(2*a) - 1`. -/
private lemma pow_add_one_dvd_pow_two_mul_sub_one' (A a : ℕ) : (A ^ a + 1) ∣ A ^ (2 * a) - 1 := by
  have h2 : A ^ (2 * a) = (A ^ a) ^ 2 := by rw [mul_comm 2 a, pow_mul]
  rw [h2]
  have hsq : (A ^ a) ^ 2 - 1 = (A ^ a + 1) * (A ^ a - 1) := by
    simpa using Nat.sq_sub_sq (A ^ a) 1
  rw [hsq]
  exact dvd_mul_right _ _

/-- The core gcd computation: `(A^(2*b)-1).gcd (A^(2*a)-1) = A^2 - 1` when `a` and `b` are
coprime. -/
private lemma gcd_pow_two_mul_sub_one {A a b : ℕ} (hcop : a.Coprime b) :
    (A ^ (2 * b) - 1).gcd (A ^ (2 * a) - 1) = A ^ 2 - 1 := by
  rw [Nat.pow_sub_one_gcd_pow_sub_one]
  have hgcd : (2 * b).gcd (2 * a) = 2 := by
    rw [Nat.gcd_mul_left, Nat.gcd_comm, hcop.gcd_eq_one, mul_one]
  rw [hgcd]

private lemma gcd_pow_add_one_pow_sub_one_dvd {A a b : ℕ} (hb : Odd b) (hcop : a.Coprime b) :
    (A ^ b + 1).gcd (A ^ a - 1) ∣ A + 1 := by
  have hg1 : (A ^ b + 1).gcd (A ^ a - 1) ∣ A ^ (2 * b) - 1 :=
    (Nat.gcd_dvd_left _ _).trans (pow_add_one_dvd_pow_two_mul_sub_one A b)
  have hg2 : (A ^ b + 1).gcd (A ^ a - 1) ∣ A ^ (2 * a) - 1 :=
    (Nat.gcd_dvd_right _ _).trans (pow_sub_one_dvd_pow_two_mul_sub_one A a)
  have hgg : (A ^ b + 1).gcd (A ^ a - 1) ∣ (A ^ (2 * b) - 1).gcd (A ^ (2 * a) - 1) :=
    Nat.dvd_gcd hg1 hg2
  have hsq : (A ^ b + 1).gcd (A ^ a - 1) ∣ A ^ 2 - 1 := by
    rw [gcd_pow_two_mul_sub_one hcop] at hgg
    exact hgg
  exact dvd_succ_of_dvd_sq_sub_one_of_dvd_pow_add_one hb hsq (Nat.gcd_dvd_left _ _)

private lemma gcd_pow_add_one_pow_add_one_dvd {A a b : ℕ} (hb : Odd b) (hcop : a.Coprime b) :
    (A ^ b + 1).gcd (A ^ a + 1) ∣ A + 1 := by
  have hg1 : (A ^ b + 1).gcd (A ^ a + 1) ∣ A ^ (2 * b) - 1 :=
    (Nat.gcd_dvd_left _ _).trans (pow_add_one_dvd_pow_two_mul_sub_one A b)
  have hg2 : (A ^ b + 1).gcd (A ^ a + 1) ∣ A ^ (2 * a) - 1 :=
    (Nat.gcd_dvd_right _ _).trans (pow_add_one_dvd_pow_two_mul_sub_one' A a)
  have hgg : (A ^ b + 1).gcd (A ^ a + 1) ∣ (A ^ (2 * b) - 1).gcd (A ^ (2 * a) - 1) :=
    Nat.dvd_gcd hg1 hg2
  have hsq : (A ^ b + 1).gcd (A ^ a + 1) ∣ A ^ 2 - 1 := by
    rw [gcd_pow_two_mul_sub_one hcop] at hgg
    exact hgg
  exact dvd_succ_of_dvd_sq_sub_one_of_dvd_pow_add_one hb hsq (Nat.gcd_dvd_left _ _)

theorem gcdPowAddOneDvd (p k i : ℕ) (h : Odd (k / i.gcd k)) :
    (p^k+1).gcd (p^i - 1) ∣ p^(i.gcd k) + 1 ∧
    (p^k+1).gcd (p^i + 1) ∣ p^(i.gcd k) + 1 := by
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Nat.gcd_zero_right, Nat.zero_div] at h
    exact absurd h (by simp [Nat.odd_iff])
  have hepos : 0 < i.gcd k := Nat.gcd_pos_of_pos_right i (by omega)
  have hcop : (i / i.gcd k).Coprime (k / i.gcd k) := Nat.coprime_div_gcd_div_gcd hepos
  have hia : (p ^ (i.gcd k)) ^ (i / i.gcd k) = p ^ i := by
    rw [← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left i k)]
  have hkb : (p ^ (i.gcd k)) ^ (k / i.gcd k) = p ^ k := by
    rw [← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right i k)]
  refine ⟨?_, ?_⟩
  · rw [← hkb, ← hia]
    exact gcd_pow_add_one_pow_sub_one_dvd h hcop
  · rw [← hkb, ← hia]
    exact gcd_pow_add_one_pow_add_one_dvd h hcop

end Work.DSTR.M110
