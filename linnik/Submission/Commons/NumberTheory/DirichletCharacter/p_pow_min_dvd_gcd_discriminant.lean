import Mathlib

set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

/-- If `p^m` divides both `a + b - c - d` and `a*b - c*d`, then `p^(min e (2m))`
divides the gcd of `p^e` with the discriminant-type product of the six pairwise
differences of `a, b, c, d`. -/
theorem p_pow_min_dvd_gcd_discriminant {p e m : ℕ} (hp : p.Prime) {a b c d : ℕ}
    (h1 : (p:ℤ)^m ∣ (a:ℤ) + (b:ℤ) - (c:ℤ) - (d:ℤ))
    (h2 : (p:ℤ)^m ∣ (a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ)) :
    p ^ (min e (2*m)) ∣ Nat.gcd (p^e)
      ((((a:ℤ)-(b:ℤ)) * ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))
        * ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) * ((c:ℤ)-(d:ℤ))).natAbs) := by
  -- Both `(a - c) * (a - d)` and `(b - c) * (b - d)` vanish modulo `p^m`.
  have ha : (p:ℤ)^m ∣ ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ)) := by
    have h := dvd_sub (dvd_mul_of_dvd_left h1 (a:ℤ)) h2
    have he : ((a:ℤ) + (b:ℤ) - (c:ℤ) - (d:ℤ)) * (a:ℤ)
        - ((a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ))
        = ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ)) := by ring
    rw [he] at h; exact h
  have hb : (p:ℤ)^m ∣ ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) := by
    have h := dvd_sub (dvd_mul_of_dvd_left h1 (b:ℤ)) h2
    have he : ((a:ℤ) + (b:ℤ) - (c:ℤ) - (d:ℤ)) * (b:ℤ)
        - ((a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ))
        = ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) := by ring
    rw [he] at h; exact h
  -- Hence `p^(2m)` divides the product of those two factors.
  have hprod : (p:ℤ)^(2*m) ∣
      (((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))) * (((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ))) := by
    rw [two_mul, pow_add]
    exact mul_dvd_mul ha hb
  -- Hence `p^(2m)` divides the full discriminant-type product.
  have hD : (p:ℤ)^(2*m) ∣ ((a:ℤ)-(b:ℤ)) * ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))
        * ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) * ((c:ℤ)-(d:ℤ)) := by
    have h := dvd_mul_of_dvd_right hprod (((a:ℤ)-(b:ℤ)) * ((c:ℤ)-(d:ℤ)))
    have he : (((a:ℤ)-(b:ℤ)) * ((c:ℤ)-(d:ℤ))) *
          ((((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))) * (((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ))))
        = ((a:ℤ)-(b:ℤ)) * ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))
          * ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) * ((c:ℤ)-(d:ℤ)) := by ring
    rw [he] at h; exact h
  -- Transfer the divisibility to the natural absolute value.
  have hDnat : p^(2*m) ∣ (((a:ℤ)-(b:ℤ)) * ((a:ℤ)-(c:ℤ)) * ((a:ℤ)-(d:ℤ))
        * ((b:ℤ)-(c:ℤ)) * ((b:ℤ)-(d:ℤ)) * ((c:ℤ)-(d:ℤ))).natAbs :=
    Int.natCast_dvd.1 (by rw [Nat.cast_pow]; exact hD)
  exact Nat.dvd_gcd (pow_dvd_pow p (min_le_left e (2*m)))
    (dvd_trans (pow_dvd_pow p (min_le_right e (2*m))) hDnat)

end Commons.NumberTheory.DirichletCharacter
