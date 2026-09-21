import Mathlib
import Submission.Work.OddRadon.RadialDefs

namespace Work.OddCurve.LowSlope

/-- Algebraic core of the sign computation: the linear combination
`(2n+1) A' + (2n+2) r B'` collapses to `(2n+1)(2n+2) R^(2n) (R+r) R'`, and
`(2n+1) A' - (2n+2) R B'` collapses to `(2n+1)(2n+2) r^(2n) (r+R) r'`.  Since the
prefactors are strictly positive (as `R, r > 0`), the signs of these combinations are
those of `R'` and `r'` respectively. -/
theorem radialSystem_deriv_sign (n : ℕ) (hn : 1 ≤ n) {A' B' R r R' r' : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (h1 : ((2 * n + 2 : ℕ) : ℝ) * R ^ (2 * n + 1) * R' +
          ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * r' = A')
    (h2 : ((2 * n + 1 : ℕ) : ℝ) * R ^ (2 * n) * R' -
          ((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * r' = B') :
    (R' ≤ 0 ↔ ((2 * n + 1 : ℕ) : ℝ) * A' + ((2 * n + 2 : ℕ) : ℝ) * r * B' ≤ 0) ∧
    (r' ≤ 0 ↔ ((2 * n + 1 : ℕ) : ℝ) * A' - ((2 * n + 2 : ℕ) : ℝ) * R * B' ≤ 0) := by
  -- rewrite the odd powers `R^(2n+1)`, `r^(2n+1)` in terms of `R^(2n)`, `r^(2n)`
  have hRn : R ^ (2 * n + 1) = R ^ (2 * n) * R := by
    rw [show 2 * n + 1 = 2 * n + 1 from rfl, pow_add, pow_one]
  have hrn : r ^ (2 * n + 1) = r ^ (2 * n) * r := by
    rw [show 2 * n + 1 = 2 * n + 1 from rfl, pow_add, pow_one]
  have hA : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * n + 1)
  have hB : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * n + 2)
  -- the two collapsing identities
  have key1 : (((2 * n + 1 : ℕ) : ℝ)) * A' + (((2 * n + 2 : ℕ) : ℝ)) * r * B'
      = ((((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * R ^ (2 * n) * (R + r)) * R' := by
    rw [← h1, ← h2, hRn, hrn]; push_cast; ring
  have key2 : (((2 * n + 1 : ℕ) : ℝ)) * A' - (((2 * n + 2 : ℕ) : ℝ)) * R * B'
      = ((((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * r ^ (2 * n) * (r + R)) * r' := by
    rw [← h1, ← h2, hRn, hrn]; push_cast; ring
  -- strict positivity of the two prefactors
  have hc : (0 : ℝ) < (((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * R ^ (2 * n) * (R + r) :=
    mul_pos (mul_pos (mul_pos hA hB) (pow_pos hR _)) (add_pos hR hr)
  have hd : (0 : ℝ) < (((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * r ^ (2 * n) * (r + R) :=
    mul_pos (mul_pos (mul_pos hA hB) (pow_pos hr _)) (add_pos hr hR)
  have hmul1 : (R' ≤ 0) ↔
      ((((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * R ^ (2 * n) * (R + r)) * R' ≤ 0 := by
    simpa using (mul_le_mul_iff_of_pos_left hc (b := R') (c := 0)).symm
  have hmul2 : (r' ≤ 0) ↔
      ((((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) * r ^ (2 * n) * (r + R)) * r' ≤ 0 := by
    simpa using (mul_le_mul_iff_of_pos_left hd (b := r') (c := 0)).symm
  exact ⟨by rw [key1]; exact hmul1, by rw [key2]; exact hmul2⟩

end Work.OddCurve.LowSlope
