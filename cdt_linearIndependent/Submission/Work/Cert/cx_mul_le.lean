import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

open Complex

noncomputable section

/-! # The one-ulp multiplicative error of the mantissa pair

The certificate represents `(x + y·i)/((S : ℝ))` by a pair of integer mantissas `(x, y)`
(`cx` in `Spec.lean`).  Multiplying two such numbers naively incurs one rounding per
integer product: `cmr a b c d = md a c - md b d` and `cmi a b c d = md a d + md b c`,
where `md x y = ⌊x·y/((S : ℝ))⌋`.

Each floor loses less than `1`, so the real and imaginary parts of the difference are each
of size `< 2/((S : ℝ))`, and the modulus is `< 2√2/((S : ℝ)) ≤ 3/((S : ℝ))`. -/

theorem cx_mul_le (a b c d : ℤ) :
    ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have h1 := md_err' a c
  have h2 := md_err' b d
  have h3 := md_err' a d
  have h4 := md_err' b c
  set z := cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d with hz
  -- the real part of the difference is `(x₁ - x₂)/S`, where each `xᵢ = md - (exact)/S`
  have hzre : z.re = ((((md a c : ℤ) : ℝ) - (a : ℝ) * (c : ℝ) / (S : ℝ)) -
      (((md b d : ℤ) : ℝ) - (b : ℝ) * (d : ℝ) / (S : ℝ))) / (S : ℝ) := by
    rw [hz]
    simp only [cmr, Complex.sub_re, Complex.mul_re, thcx_re, thcx_im]
    push_cast
    ring_nf
  have hzim : z.im = ((((md a d : ℤ) : ℝ) - (a : ℝ) * (d : ℝ) / (S : ℝ)) +
      (((md b c : ℤ) : ℝ) - (b : ℝ) * (c : ℝ) / (S : ℝ))) / (S : ℝ) := by
    rw [hz]
    simp only [cmi, Complex.sub_im, Complex.mul_im, thcx_re, thcx_im]
    push_cast
    ring_nf
  have hre : |z.re| ≤ 2 / (S : ℝ) := by
    have hsub : |(((md a c : ℤ) : ℝ) - (a : ℝ) * (c : ℝ) / (S : ℝ)) -
        (((md b d : ℤ) : ℝ) - (b : ℝ) * (d : ℝ) / (S : ℝ))| < 2 := by
      have p1 := abs_lt.mp h1
      have p2 := abs_lt.mp h2
      rw [abs_lt]; constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]
    rw [hzre, abs_div, abs_of_pos hS]
    exact le_of_lt (div_lt_div_of_pos_right hsub hS)
  have him : |z.im| ≤ 2 / (S : ℝ) := by
    have hsum : |(((md a d : ℤ) : ℝ) - (a : ℝ) * (d : ℝ) / (S : ℝ)) +
        (((md b c : ℤ) : ℝ) - (b : ℝ) * (c : ℝ) / (S : ℝ))| < 2 := by
      have p3 := abs_lt.mp h3
      have p4 := abs_lt.mp h4
      rw [abs_lt]; constructor <;> linarith [p3.1, p3.2, p4.1, p4.2]
    rw [hzim, abs_div, abs_of_pos hS]
    exact le_of_lt (div_lt_div_of_pos_right hsum hS)
  have hsq : ‖z‖ ^ 2 ≤ (3 / (S : ℝ)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have p := abs_le.mp hre
    have q := abs_le.mp him
    have e1 : z.re * z.re ≤ (2 / (S : ℝ)) ^ 2 := by nlinarith [p.1, p.2]
    have e2 : z.im * z.im ≤ (2 / (S : ℝ)) ^ 2 := by nlinarith [q.1, q.2]
    have e3 : (2 / (S : ℝ)) ^ 2 + (2 / (S : ℝ)) ^ 2 ≤ (3 / (S : ℝ)) ^ 2 := by
      have hS2 : (0 : ℝ) < (S : ℝ) ^ 2 := sq_pos_of_pos hS
      rw [show (2 / (S : ℝ)) ^ 2 + (2 / (S : ℝ)) ^ 2 = 8 / (S : ℝ) ^ 2 by ring,
          show (3 / (S : ℝ)) ^ 2 = 9 / (S : ℝ) ^ 2 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hS2)
    linarith [e1, e2, e3]
  have hnorm : ‖z‖ ≤ 3 / (S : ℝ) := by
    have hh := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 3 / (S : ℝ)))] at hh
  exact hnorm

end

end Work.Cert
