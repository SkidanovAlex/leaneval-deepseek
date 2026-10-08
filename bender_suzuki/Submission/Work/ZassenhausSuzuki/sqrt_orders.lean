import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- Classification of the two integer solutions of the system
`a + b = 2q + 2`, `a * b = q^2 + 1` when `q = 2^m` with `m` odd:
they are `q + 1 ± 2^((m+1)/2)`.

Indeed `a` and `b` are the roots of `X^2 - (2q+2)X + (q^2+1)`, whose discriminant is
`(2q+2)^2 - 4(q^2+1) = 8q = 4·2^m·2 = (2·2^((m+1)/2))^2` because `m` odd makes
`(m+1)/2` an integer. -/
theorem sqrt_orders {m q a b : ℕ} (hm : Odd m) (hq : q = 2 ^ m)
    (hab : a + b = 2 * q + 2) (hab2 : a * b = q ^ 2 + 1) :
    (a = q + 1 + 2 ^ ((m + 1) / 2) ∧ b = q + 1 - 2 ^ ((m + 1) / 2)) ∨
      (a = q + 1 - 2 ^ ((m + 1) / 2) ∧ b = q + 1 + 2 ^ ((m + 1) / 2)) := by
  obtain ⟨k, rfl⟩ := hm
  have hm1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [hm1]
  -- The square root `s = 2^(k+1)` satisfies `s^2 = 2*q`.
  have hs2 : (2 ^ (k + 1)) ^ 2 = 2 * q := by
    rw [hq, ← pow_mul]
    rw [show (k + 1) * 2 = 2 * k + 2 by ring]
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, pow_succ]
    ring
  -- Transfer the two symmetric relations to `ℤ`.
  have hsum : (a : ℤ) + (b : ℤ) = 2 * (q : ℤ) + 2 := by exact_mod_cast hab
  have hprod : (a : ℤ) * (b : ℤ) = (q : ℤ) ^ 2 + 1 := by exact_mod_cast hab2
  -- Vieta: `(a - (q+1))^2 = 2q = s^2`.
  have hkey : ((a : ℤ) - ((q : ℤ) + 1)) ^ 2 = ((2 : ℤ) ^ (k + 1)) ^ 2 := by
    have h1 : ((a : ℤ) - ((q : ℤ) + 1)) ^ 2
        = ((q : ℤ) + 1) ^ 2 - ((q : ℤ) ^ 2 + 1) := by
      nlinarith [hsum, hprod]
    rw [h1]
    have h2 : ((q : ℤ) + 1) ^ 2 - ((q : ℤ) ^ 2 + 1) = 2 * (q : ℤ) := by ring
    rw [h2]
    have h3 := congrArg (Nat.cast : ℕ → ℤ) hs2
    push_cast at h3
    linarith [h3]
  -- Hence `a - (q+1) = ± 2^(k+1)`.
  have hfac : (((a : ℤ) - ((q : ℤ) + 1)) - (2 : ℤ) ^ (k + 1)) *
      (((a : ℤ) - ((q : ℤ) + 1)) + (2 : ℤ) ^ (k + 1)) = 0 := by
    nlinarith [hkey]
  rcases mul_eq_zero.mp hfac with h | h
  · -- Case `a - (q+1) = +s`.
    have haZ : (a : ℤ) = (q : ℤ) + 1 + (2 : ℤ) ^ (k + 1) := by linarith
    have ha : a = q + 1 + 2 ^ (k + 1) := by exact_mod_cast haZ
    have hbZ : (b : ℤ) = (q : ℤ) + 1 - (2 : ℤ) ^ (k + 1) := by linarith [hsum, haZ]
    have hleZ : (2 : ℤ) ^ (k + 1) ≤ (q : ℤ) + 1 := by
      have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
      linarith [hbZ, hb0]
    have hle : 2 ^ (k + 1) ≤ q + 1 := by exact_mod_cast hleZ
    have hb : b = q + 1 - 2 ^ (k + 1) := by
      have hcast : (b : ℤ) = ((q + 1 - 2 ^ (k + 1) : ℕ) : ℤ) := by
        rw [hbZ, Nat.cast_sub hle]
        push_cast
        ring
      exact Nat.cast_injective hcast
    exact Or.inl ⟨ha, hb⟩
  · -- Case `a - (q+1) = -s`.
    have haZ : (a : ℤ) = (q : ℤ) + 1 - (2 : ℤ) ^ (k + 1) := by linarith
    have hleZ : (2 : ℤ) ^ (k + 1) ≤ (q : ℤ) + 1 := by
      have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
      linarith [haZ, ha0]
    have hle : 2 ^ (k + 1) ≤ q + 1 := by exact_mod_cast hleZ
    have ha : a = q + 1 - 2 ^ (k + 1) := by
      have hcast : (a : ℤ) = ((q + 1 - 2 ^ (k + 1) : ℕ) : ℤ) := by
        rw [haZ, Nat.cast_sub hle]
        push_cast
        ring
      exact Nat.cast_injective hcast
    have hbZ : (b : ℤ) = (q : ℤ) + 1 + (2 : ℤ) ^ (k + 1) := by linarith [hsum, haZ]
    have hb : b = q + 1 + 2 ^ (k + 1) := by exact_mod_cast hbZ
    exact Or.inr ⟨ha, hb⟩

end Work.ZassenhausSuzuki
