import Mathlib

namespace Work.DSTR.M110

/-- Auxiliary polynomial estimate: for `A ≥ 5`, `(A + 1)^3 ≤ 2 * A^3`.
Equivalently `A^3 - 3A^2 - 3A - 1 ≥ 0`, which holds for `A ≥ 5` (value `34` at `A = 5`,
increasing thereafter). -/
private lemma cube_add_one_le (A : ℕ) (hA5 : 5 ≤ A) : (A + 1) ^ 3 ≤ 2 * A ^ 3 := by
  have h : (A : ℤ) ≥ 5 := by omega
  nlinarith [sq_nonneg ((A : ℤ)), sq_nonneg ((A : ℤ) - 5)]

/-- Gorenstein–Walter arithmetic core.  For `A ≥ 5` and odd `q ≥ 3` with `2 * q ≤ A + 1`
(so `q ≤ (A + 1) / 2`), the polynomial `q * (A + 1)^2` is dominated by `A^q + 1`.

The estimate is sharp at the boundary `A = 5`, `q = 3`: `3 * 6^2 = 108 < 126 = 5^3 + 1`. -/
theorem powAddOneArithCore (A q : ℕ) (hA5 : 5 ≤ A) (hqodd : Odd q) (hq3 : 3 ≤ q) (h2q : 2 * q ≤ A + 1) :
    q * (A + 1) ^ 2 < A ^ q + 1 := by
  have hqpos : 0 < q := hqodd.pos
  have hApos : 0 < A := by omega
  -- Step 1: `(A + 1)^3 ≤ 2 * A^3`.
  have hcube : (A + 1) ^ 3 ≤ 2 * A ^ 3 := cube_add_one_le A hA5
  -- Step 2: `A^3 ≤ A^q` since `3 ≤ q`.
  have hA3 : A ^ 3 ≤ A ^ q := Nat.pow_le_pow_right hApos hq3
  -- Step 3: `(A + 1)^3 ≤ 2 * A^q`.
  have h2 : (A + 1) ^ 3 ≤ 2 * A ^ q := le_trans hcube (Nat.mul_le_mul_left 2 hA3)
  -- Step 4: `q * (A + 1)^2 * 2 = (2 * q) * (A + 1)^2 ≤ (A + 1) * (A + 1)^2 = (A + 1)^3`.
  have h3 : q * (A + 1) ^ 2 * 2 ≤ (A + 1) ^ 3 := by
    have e : q * (A + 1) ^ 2 * 2 = (2 * q) * (A + 1) ^ 2 := by ring
    rw [e]
    calc (2 * q) * (A + 1) ^ 2 ≤ (A + 1) * (A + 1) ^ 2 :=
          Nat.mul_le_mul_right _ h2q
      _ = (A + 1) ^ 3 := by ring
  -- Step 5: `q * (A + 1)^2 * 2 ≤ 2 * A^q`, cancel the factor `2`.
  have h4 : q * (A + 1) ^ 2 * 2 ≤ 2 * A ^ q := le_trans h3 h2
  have h5 : q * (A + 1) ^ 2 ≤ A ^ q := by
    rw [mul_comm (q * (A + 1) ^ 2) 2] at h4
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  exact Nat.lt_succ_of_le h5

end Work.DSTR.M110
