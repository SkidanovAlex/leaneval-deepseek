import Mathlib

namespace Work.DSTR.M110

/-- For odd `q`, the quotient `(A^q + 1) / (A + 1)` is odd.

This is the 2-adic companion of the LTE statement `v_2(A^q + 1) = v_2(A + 1)` for odd `q`.
Equivalently `(A^q + 1)/(A + 1)` is odd because it equals the alternating sum
`1 - A + A² - ⋯ + A^{q-1}`.

The proof avoids any `ZMod`/sum machinery and proceeds purely in `ℕ`:
dividing `A^q + 1 = (A + 1)·B` by `A + 1` and subtracting `1` gives

`(A + 1)·(B - 1) = A^q - A = A·(A^{q-1} - 1) = A·((A²)^{(q-1)/2} - 1)`,

and since `A² - 1 = (A + 1)(A - 1)` divides `(A²)^{(q-1)/2} - 1`, while `A(A - 1)` is even,
we may cancel `A + 1` to conclude `B - 1` is even, i.e. `B` is odd. -/
theorem quotientPowAddOneOdd (A q : ℕ) (hq : Odd q) : Odd ((A ^ q + 1) / (A + 1)) := by
  have hdvd : A + 1 ∣ A ^ q + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow A 1 hq
  have hmul : (A + 1) * ((A ^ q + 1) / (A + 1)) = A ^ q + 1 := Nat.mul_div_cancel' hdvd
  obtain ⟨e, he⟩ := hq
  have he2 : q = 2 * e + 1 := by omega
  -- `A * (A - 1)` is even.
  obtain ⟨s, hs⟩ : ∃ s, A * (A - 1) = 2 * s := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self A
    exact ⟨k, by omega⟩
  -- `A^2 - 1` divides `(A^2)^e - 1`.
  obtain ⟨t, ht⟩ := Nat.sub_one_dvd_pow_sub_one (A ^ 2) e
  -- Subtracting `1` from the quotient and multiplying by `A + 1` recovers `A^q - A`.
  have hmain : (A + 1) * ((A ^ q + 1) / (A + 1) - 1) = A ^ q - A := by
    rw [Nat.mul_sub_left_distrib, hmul, mul_one, Nat.add_sub_add_right]
  -- `A^q - A = (A + 1) * (2 * (s * t))` is divisible by `2 * (A + 1)`.
  have hkey : A ^ q - A = (A + 1) * (2 * (s * t)) := by
    have hAq : A ^ q = A * (A ^ 2) ^ e := by
      rw [he2, pow_succ, pow_mul, mul_comm]
    have h1 : A ^ q - A = A * ((A ^ 2) ^ e - 1) := by
      rw [hAq, Nat.mul_sub_left_distrib, mul_one]
    have h3 : A * ((A ^ 2 - 1) * t) = (A + 1) * (2 * (s * t)) := by
      have hsq : A ^ 2 - 1 = (A + 1) * (A - 1) := by simpa using Nat.sq_sub_sq A 1
      calc A * ((A ^ 2 - 1) * t)
          = (A * (A - 1)) * ((A + 1) * t) := by rw [hsq]; ring
        _ = (2 * s) * ((A + 1) * t) := by rw [hs]
        _ = (A + 1) * (2 * (s * t)) := by ring
    calc A ^ q - A = A * ((A ^ 2) ^ e - 1) := h1
      _ = A * ((A ^ 2 - 1) * t) := by rw [ht]
      _ = (A + 1) * (2 * (s * t)) := h3
  -- Cancel the factor `A + 1 > 0`.
  have hcancel : (A ^ q + 1) / (A + 1) - 1 = 2 * (s * t) := by
    have heq : (A + 1) * ((A ^ q + 1) / (A + 1) - 1) = (A + 1) * (2 * (s * t)) :=
      hmain.trans hkey
    exact Nat.mul_left_cancel (show 0 < A + 1 by omega) heq
  have hBpos : 1 ≤ (A ^ q + 1) / (A + 1) := by
    have hle : A + 1 ≤ A ^ q + 1 := by
      have h1 : A ≤ A ^ q := Nat.le_self_pow (by omega : q ≠ 0) A
      omega
    exact Nat.div_pos hle (by omega)
  exact ⟨s * t, Nat.eq_add_of_sub_eq hBpos hcancel⟩

end Work.DSTR.M110
