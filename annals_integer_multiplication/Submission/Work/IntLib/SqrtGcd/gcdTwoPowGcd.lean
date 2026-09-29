import Mathlib

/-!
# `gcd (2 ^ i * p) (2 ^ j * q)` for odd `p`, `q`

The odd part of `2 ^ i * p` (for odd `p`) is `p`, and powers of two contribute to the gcd exactly
the smaller exponent.  The main result is

`Nat.gcd (2 ^ i * p) (2 ^ j * q) = 2 ^ min i j * Nat.gcd p q`.

The elementary ingredient is that a factor coprime to `a` can be deleted from the second argument
of `Nat.gcd a _`.
-/

set_option autoImplicit false

namespace Work.IntLib.SqrtGcd

/-- A factor coprime to `a` may be deleted from the second argument of `Nat.gcd a _`. -/
theorem gcd_mul_right_of_coprime (a b c : ℕ) (h : Nat.Coprime a b) :
    Nat.gcd a (b * c) = Nat.gcd a c := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine Nat.dvd_gcd (Nat.gcd_dvd_left a (b * c)) ?_
    exact (h.coprime_dvd_left (Nat.gcd_dvd_left a (b * c))).dvd_of_dvd_mul_left
      (Nat.gcd_dvd_right a (b * c))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left a c)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right a c) b)

/-- For odd `p`, the power-of-two factor may be deleted from the second argument. -/
theorem gcd_odd_two_pow_mul (p k q : ℕ) (hp : p % 2 = 1) :
    Nat.gcd p (2 ^ k * q) = Nat.gcd p q :=
  gcd_mul_right_of_coprime p (2 ^ k) q
    ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hp)).pow_right k)

/-- For odd `q`, the power-of-two factor may be deleted from the first argument. -/
theorem gcd_two_pow_mul_odd (k p q : ℕ) (hq : q % 2 = 1) :
    Nat.gcd (2 ^ k * p) q = Nat.gcd p q :=
  calc Nat.gcd (2 ^ k * p) q = Nat.gcd q (2 ^ k * p) := Nat.gcd_comm _ _
    _ = Nat.gcd q p := gcd_odd_two_pow_mul q k p hq
    _ = Nat.gcd p q := Nat.gcd_comm _ _

theorem gcdTwoPowGcd (i j p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) :
    Nat.gcd (2 ^ i * p) (2 ^ j * q) = 2 ^ min i j * Nat.gcd p q := by
  rcases Nat.le_total i j with hij | hji
  · have hmin : min i j = i := min_eq_left hij
    have hsplit : (2 : ℕ) ^ j = 2 ^ i * 2 ^ (j - i) := by
      rw [← Nat.pow_add]; congr 1; omega
    have harg : 2 ^ j * q = 2 ^ i * (2 ^ (j - i) * q) := by rw [hsplit, mul_assoc]
    have key : Nat.gcd (2 ^ i * p) (2 ^ i * (2 ^ (j - i) * q)) = 2 ^ i * Nat.gcd p q := by
      rw [Nat.gcd_mul_left, gcd_odd_two_pow_mul p (j - i) q hp]
    rw [hmin, harg]
    exact key
  · have hmin : min i j = j := min_eq_right hji
    have hsplit : (2 : ℕ) ^ i = 2 ^ j * 2 ^ (i - j) := by
      rw [← Nat.pow_add]; congr 1; omega
    have harg : 2 ^ i * p = 2 ^ j * (2 ^ (i - j) * p) := by rw [hsplit, mul_assoc]
    have key : Nat.gcd (2 ^ j * (2 ^ (i - j) * p)) (2 ^ j * q) = 2 ^ j * Nat.gcd p q := by
      rw [Nat.gcd_mul_left, gcd_two_pow_mul_odd (i - j) p q hq]
    rw [hmin, harg]
    exact key

end Work.IntLib.SqrtGcd
