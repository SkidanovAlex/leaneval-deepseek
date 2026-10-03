import Mathlib

namespace Work.FIArea7

/-- Auxiliary real-variable comparison form of the trivial-range estimate. For
reals `x, y ≥ 1`, constants `C8, CB > 0` and any real `l`, if `x^{1/60} < y` and
`16 C8 x^{1/77} l ≤ CB x^{7/480}`, then `16 C8 y^{1/8} x l ≤ CB y x^{76/77}`.

The proof goes by writing the target left side as
`(16 C8 x^{1/77} l)·(y^{1/8} x^{76/77})` (using `x^{1/77}·x^{76/77} = x`), multiplying
the hypothesis by the nonnegative factor `y^{1/8} x^{76/77}`, and finally replacing
`x^{7/480} ≤ y^{7/8}` (which follows by raising `x^{1/60} < y` to the power `7/8`)
together with `y^{7/8}·y^{1/8} = y`. -/
private lemma t2psi_cmp_triv_aux {x y C8 CB l : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (_hC8 : 0 < C8) (hCB : 0 < CB)
    (hxbig : x ^ ((1:ℝ)/60) < y)
    (h : 16 * C8 * x ^ ((1:ℝ)/77) * l ≤ CB * x ^ ((7:ℝ)/480)) :
    16 * C8 * y ^ ((1:ℝ)/8) * x * l ≤ CB * y * x ^ ((76:ℝ)/77) := by
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : (0:ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have ha : x ^ ((1:ℝ)/77) * x ^ ((76:ℝ)/77) = x := by
    rw [← Real.rpow_add hxpos, show (1:ℝ)/77 + 76/77 = 1 by norm_num, Real.rpow_one]
  have hb : y ^ ((7:ℝ)/8) * y ^ ((1:ℝ)/8) = y := by
    rw [← Real.rpow_add hypos, show (7:ℝ)/8 + 1/8 = 1 by norm_num, Real.rpow_one]
  have h3 : x ^ ((7:ℝ)/480) ≤ y ^ ((7:ℝ)/8) := by
    have hlt := Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hxpos) ((1:ℝ)/60)) hxbig
      (by norm_num : (0:ℝ) < (7:ℝ)/8)
    rw [← Real.rpow_mul (le_of_lt hxpos) ((1:ℝ)/60) ((7:ℝ)/8),
      show (1:ℝ)/60 * ((7:ℝ)/8) = (7:ℝ)/480 by norm_num] at hlt
    exact le_of_lt hlt
  have hFnn : (0:ℝ) ≤ y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt hypos) _) (Real.rpow_nonneg (le_of_lt hxpos) _)
  have hstep : (16 * C8 * x ^ ((1:ℝ)/77) * l) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77))
      ≤ (CB * x ^ ((7:ℝ)/480)) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77)) :=
    mul_le_mul_of_nonneg_right h hFnn
  have hK : (0:ℝ) ≤ CB * y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77) :=
    mul_nonneg (mul_nonneg (le_of_lt hCB) (Real.rpow_nonneg (le_of_lt hypos) _))
      (Real.rpow_nonneg (le_of_lt hxpos) _)
  have h4 : (CB * x ^ ((7:ℝ)/480)) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77))
      ≤ CB * y * x ^ ((76:ℝ)/77) := by
    calc (CB * x ^ ((7:ℝ)/480)) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77))
        = (CB * y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77)) * x ^ ((7:ℝ)/480) := by ring
      _ ≤ (CB * y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77)) * y ^ ((7:ℝ)/8) :=
          mul_le_mul_of_nonneg_left h3 hK
      _ = CB * y * x ^ ((76:ℝ)/77) := by
          conv_rhs => rw [← hb]
          ring
  calc 16 * C8 * y ^ ((1:ℝ)/8) * x * l
      = (16 * C8 * x ^ ((1:ℝ)/77) * l) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77)) := by
        conv_lhs => rw [← ha]
        ring
    _ ≤ (CB * x ^ ((7:ℝ)/480)) * (y ^ ((1:ℝ)/8) * x ^ ((76:ℝ)/77)) := hstep
    _ ≤ CB * y * x ^ ((76:ℝ)/77) := h4

/-- Arithmetic comparison for the trivial bound in the range `c > N^{1/60}`: from
`c^{7/8} > N^{7/480}` and `16 C₈ N^{1/77} (log(N+2))^3 ≤ CB N^{7/480}` one gets
`16 C₈ c^{1/8} N (log(N+2))^3 ≤ CB c N^{76/77}`. -/
theorem t2psi_cmp_triv (N c d : ℕ) (k : ℤ) (C8 CB : ℝ)
    (hN : 2 ≤ N) (hc : 1 ≤ c) (hd : 1 ≤ d) (hC8 : 0 < C8) (hCB : 0 < CB)
    (hcbig : (N : ℝ) ^ ((1:ℝ)/60) < (c : ℝ))
    (hCB' : 16 * C8 * (N : ℝ) ^ ((1:ℝ)/77) * (Real.log ((N : ℝ) + 2)) ^ (3:ℝ)
        ≤ CB * (N : ℝ) ^ ((7:ℝ)/480)) :
    16 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (3:ℕ)
      ≤ CB * (c : ℝ) * (N : ℝ) ^ ((76:ℝ)/77) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have : (1:ℕ) ≤ N := by omega
    exact_mod_cast this
  have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  rw [← Real.rpow_natCast]
  exact t2psi_cmp_triv_aux hN1 hc1 hC8 hCB hcbig hCB'

end Work.FIArea7
