import Mathlib

namespace Work.WilE5.Bounds

/-- Crude polynomial growth comparison.

Writing `m = M+1` and `N = M+D+1`, the two factors appearing on the left are
bounded by the two on the right as follows:
* `2*(3 + q*m^q) ≤ (2*(q+3)) * N^q`, since `m ≤ N` and `1 ≤ N`; raising to the
  `q`-th power gives `(2*(q+3))^q * N^(q*q)`;
* `3*D + 3*q + 4 ≤ (3*q+7) * N`, using `N ≥ D+1`.
Multiplying and using `N^(q*q) * N = N^(q*q+1) = N^(q^2+1)` yields the claim. -/
theorem Bnd_le_poly {q M D : ℕ} :
    (2 * (3 + q * (M + 1) ^ q)) ^ q * (3 * D + 3 * q + 4) ≤
      ((6 + 2 * q) ^ q * (3 * q + 7)) * (M + D + 1) ^ (q ^ 2 + 1) := by
  have hNle : M + 1 ≤ M + D + 1 := by omega
  have hD1 : D + 1 ≤ M + D + 1 := by omega
  have hNpos : 0 < (M + D + 1) ^ q := by positivity
  have hm : (M + 1) ^ q ≤ (M + D + 1) ^ q := Nat.pow_le_pow_left hNle q
  have h3 : 3 ≤ 3 * (M + D + 1) ^ q := Nat.le_mul_of_pos_right 3 hNpos
  have hsum : 3 + q * (M + 1)^q ≤ 3 * (M + D + 1)^q + q * (M + D + 1)^q :=
    add_le_add h3 (Nat.mul_le_mul_left q hm)
  have hstep1 : 2 * (3 + q * (M + 1)^q) ≤ (2*(q+3)) * (M + D + 1)^q := by
    have h1 : 2 * (3 + q * (M + 1)^q) ≤ 2 * (3 * (M + D + 1)^q + q * (M + D + 1)^q) :=
      Nat.mul_le_mul_left 2 hsum
    have h2 : 2 * (3 * (M + D + 1)^q + q * (M + D + 1)^q)
        = (2*(q+3)) * (M + D + 1)^q := by ring
    linarith
  have hstep2 : (2 * (3 + q * (M + 1)^q))^q ≤ (2*(q+3))^q * (M + D + 1)^(q*q) := by
    calc (2 * (3 + q * (M + 1)^q))^q
        ≤ ((2*(q+3)) * (M + D + 1)^q)^q := Nat.pow_le_pow_left hstep1 q
      _ = (2*(q+3))^q * (M + D + 1)^(q*q) := by rw [mul_pow, pow_mul]
  have hD3 : 3 * D + 3 * q + 4 ≤ (3*q+7) * (D+1) := by nlinarith
  have hstep3 : 3 * D + 3 * q + 4 ≤ (3*q+7) * (M + D + 1) := by
    have h3' : (3*q+7)*(D+1) ≤ (3*q+7)*(M+D+1) := Nat.mul_le_mul_left _ hD1
    linarith
  have hfinal : ((2*(q+3))^q * (M + D + 1)^(q*q)) * ((3*q+7)*(M+D+1))
      = ((2*(q+3))^q * (3*q+7)) * (M + D + 1)^(q*q+1) := by
    rw [show (M+D+1)^(q*q+1) = (M+D+1)^(q*q) * (M+D+1) from pow_succ _ _]
    ring
  have hbase : 6 + 2*q = 2*(q+3) := by ring
  have hexp : q^2 + 1 = q*q+1 := by rw [pow_two]
  calc (2 * (3 + q * (M + 1) ^ q)) ^ q * (3 * D + 3 * q + 4)
      ≤ ((2*(q+3))^q * (M + D + 1)^(q*q)) * ((3*q+7)*(M+D+1)) :=
        Nat.mul_le_mul hstep2 hstep3
    _ = ((2*(q+3))^q * (3*q+7)) * (M + D + 1)^(q*q+1) := hfinal
    _ = ((6 + 2 * q) ^ q * (3 * q + 7)) * (M + D + 1) ^ (q ^ 2 + 1) := by
        rw [hbase, hexp]

end Work.WilE5.Bounds
