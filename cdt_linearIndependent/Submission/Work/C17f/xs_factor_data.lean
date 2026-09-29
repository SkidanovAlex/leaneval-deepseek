import Mathlib
import Submission.Work.C17.logP_local_defs
import Submission.Work.C17.logP_local_plan
import Submission.Work.C17.led_factor
import Submission.Work.C17.led_real_data
import Submission.Work.C17.holo_Kfun

/-!
# The algebraic data at the cusp `x_s`

Auxiliary real/complex lemmas about the cusp `x_s = (a+√(a²−1))(b−√(b²−1))` and the
factorisation `P2x = (X − x_s)·Q2x` at `x_s`, used downstream by the local-structure analysis of
`Pfun` (`Submission.Work.C17.logP_local_structure`).
-/

namespace Work.C17f

open Polynomial
open Work.C17

noncomputable section

/-- `x_s ≠ 0`. -/
private lemma xs_ne (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) : xs a b ≠ 0 := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hsb : 0 ≤ (b : ℝ) ^ 2 - 1 := by nlinarith
  have ht2 : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 := Real.sq_sqrt hsb
  have h1 : (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) ≠ 0 := by
    have hs := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1)
    have : (0 : ℝ) < (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) := by nlinarith
    exact ne_of_gt this
  have h2 : (b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1) ≠ 0 := by
    intro h
    have hB : ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1))
        * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) = 1 := by nlinarith [ht2]
    rw [h, zero_mul] at hB
    exact one_ne_zero hB.symm
  have hxseq : xs a b
      = ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) := rfl
  rw [hxseq]
  exact mul_ne_zero h1 h2

/-- The real identity `x_s + 1/x_s = ledD` at the cusp. -/
private lemma xs_add_inv (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    xs a b + 1 / xs a b = ledD a b := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hsa : 0 ≤ (a : ℝ) ^ 2 - 1 := by nlinarith
  have hsb : 0 ≤ (b : ℝ) ^ 2 - 1 := by nlinarith
  have hs2 : Real.sqrt ((a : ℝ) ^ 2 - 1) ^ 2 = (a : ℝ) ^ 2 - 1 := Real.sq_sqrt hsa
  have ht2 : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 := Real.sq_sqrt hsb
  have hst : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1))
      = Real.sqrt ((a : ℝ) ^ 2 - 1) * Real.sqrt ((b : ℝ) ^ 2 - 1) := Real.sqrt_mul hsa _
  have hA : ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1))
      = 1 := by nlinarith [hs2]
  have hB : ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1))
      = 1 := by nlinarith [ht2]
  have hunit : (((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)))
      * (((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1))) = 1 := by
    rw [show ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1))
          * (((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)))
        = (((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)))
          * (((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)))
        from by ring,
      hA, hB, mul_one]
  have hxs_eq : xs a b
      = ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) := rfl
  have hxs_ne : xs a b ≠ 0 := xs_ne a b ha hb
  have hinv : 1 / xs a b
      = ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) := by
    rw [div_eq_iff hxs_ne, hxs_eq]
    exact hunit.symm
  rw [hinv, hxs_eq, ledD, hst]
  ring

/-- The real identity `x_s ^ 2 + 1 = ledD · x_s` at the cusp. -/
private lemma xs_sq_plus_one (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    xs a b ^ 2 + 1 = ledD a b * xs a b := by
  have h := xs_add_inv a b ha hb
  have hne : xs a b ≠ 0 := xs_ne a b ha hb
  have h2 : xs a b * (xs a b + 1 / xs a b) = xs a b * ledD a b := by rw [h]
  rw [mul_add, mul_one_div, div_self hne] at h2
  rw [mul_comm (xs a b) (ledD a b)] at h2
  simpa only [pow_two] using h2

/-- The complex identity `x_s ^ 2 − ledD·x_s + 1 = 0`. -/
private lemma xsC_sq_sub (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    xsC a b ^ 2 - ((ledD a b : ℝ) : ℂ) * xsC a b + 1 = 0 := by
  have h := xs_sq_plus_one a b ha hb
  have h' : (((xs a b) ^ 2 - ledD a b * xs a b + 1 : ℝ) : ℂ) = 0 := by
    rw [show xs a b ^ 2 - ledD a b * xs a b + 1 = 0 from by linarith]; norm_num
  push_cast at h'
  simpa [xsC] using h'

/-- The complex identity `x_s + 1/x_s = ledD`. -/
private lemma xsC_add_inv (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    xsC a b + ((1 / xs a b : ℝ) : ℂ) = ((ledD a b : ℝ) : ℂ) := by
  have h := xs_add_inv a b ha hb
  have h' : (((xs a b + 1 / xs a b) : ℝ) : ℂ) = ((ledD a b : ℝ) : ℂ) := by rw [h]
  push_cast at h'
  simpa [xsC] using h'

/-- The complex identity `x_s · (1/x_s) = 1`. -/
private lemma xsC_mul_inv (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    xsC a b * ((1 / xs a b : ℝ) : ℂ) = 1 := by
  have hne : xs a b ≠ 0 := xs_ne a b ha hb
  have h : ((xs a b * (1 / xs a b) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [mul_one_div, div_self hne]
  push_cast at h
  simpa [xsC] using h

theorem xs_factor_data (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (hQ4 : (Work.C17.Q4x a b).eval₂ (algebraMap ℚ ℂ) (Work.C17.xsC a b) = 0) :
    (Work.C17.P2x a b).map (algebraMap ℚ ℂ)
        = (Polynomial.X - Polynomial.C (Work.C17.xsC a b)) * Work.C17.Q2x a b ∧
      (Work.C17.Q2x a b).eval (Work.C17.xsC a b) ≠ 0 ∧
      (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) (Work.C17.xsC a b)
        = (Work.C17.Q2x a b).eval (Work.C17.xsC a b) ∧
      ∃ S : Polynomial ℂ,
        (Work.C17.P1x a b).map (algebraMap ℚ ℂ)
            - Polynomial.C ((Work.C17.Q2x a b).eval (Work.C17.xsC a b))
          = (Polynomial.X - Polynomial.C (Work.C17.xsC a b)) * S := by
  obtain ⟨hxs_pos, hxs_lt1⟩ := xs_pos_and_lt_one a b ha hb hab
  have hsumC : xsC a b + ((1 / xs a b : ℝ) : ℂ) = ((ledD a b : ℝ) : ℂ) :=
    xsC_add_inv a b ha hb
  have hmulC : xsC a b * ((1 / xs a b : ℝ) : ℂ) = 1 := xsC_mul_inv a b ha hb
  have hxsD : xsC a b ^ 2 - ((ledD a b : ℝ) : ℂ) * xsC a b + 1 = 0 := xsC_sq_sub a b ha hb
  have h2z : (2 : ℂ) * xsC a b - ((ledD a b : ℝ) : ℂ)
      = xsC a b - ((1 / xs a b : ℝ) : ℂ) := by
    rw [← hsumC]; ring
  -- the quadratic identity `X² − ledD·X + 1 = (X − x_s)(X − 1/x_s)`
  have hquad : (Polynomial.X ^ 2 - Polynomial.C (((ledD a b : ℝ) : ℂ)) * Polynomial.X + 1
        : Polynomial ℂ)
      = (Polynomial.X - Polynomial.C (xsC a b))
        * (Polynomial.X - Polynomial.C ((1 / xs a b : ℝ) : ℂ)) := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    rw [← hsumC, ← hmulC]
    ring
  -- part 1: `P2x = (X − x_s)·Q2x`
  have hmap3 : (((Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1) : Polynomial ℚ)).map
        (algebraMap ℚ ℂ)
      = (Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1) := by
    simp
  have hQ2x_body : Q2x a b = (Polynomial.X - Polynomial.C ((1 / xs a b : ℝ) : ℂ))
      * (Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1)
      * (Polynomial.X ^ 2 - Polynomial.C (((ledC a b : ℝ) : ℂ)) * Polynomial.X + 1) := rfl
  have h1 : (P2x a b).map (algebraMap ℚ ℂ)
      = (Polynomial.X - Polynomial.C (xsC a b)) * Q2x a b := by
    rw [show P2x a b = ((Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1)) * Q4x a b
        from rfl,
      Polynomial.map_mul, hmap3, led_factor a b ha hb, hquad, hQ2x_body]
    ring
  -- part 2: `Q2x x_s ≠ 0`
  have hxsC_ne0 : xsC a b ≠ 0 := by
    intro h
    exact xs_ne a b ha hb (Complex.ofReal_eq_zero.mp (by simpa [xsC] using h))
  have hxsC_ne1 : xsC a b ≠ 1 := by
    intro h
    have h' : ((xs a b : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by simpa [xsC] using h
    have h2 : xs a b = 1 := Complex.ofReal_inj.mp h'
    nlinarith [hxs_lt1, h2]
  have hxsC_nem1 : xsC a b ≠ -1 := by
    intro h
    have h' : ((xs a b : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by simpa [xsC] using h
    have h2 : xs a b = -1 := Complex.ofReal_inj.mp h'
    linarith [hxs_pos, h2]
  have hxsC_ne_YC : xsC a b - ((1 / xs a b : ℝ) : ℂ) ≠ 0 := by
    intro h
    have hz : xsC a b = ((1 / xs a b : ℝ) : ℂ) := sub_eq_zero.mp h
    have hsq : xsC a b * xsC a b = 1 := by rw [← hmulC, ← hz]
    have hreal : xs a b * xs a b = 1 := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_mul, Complex.ofReal_one]
      simpa [xsC] using hsq
    linarith [hxs_lt1, hreal]
  have hLCne : ((ledC a b : ℝ) : ℂ) ≠ ((ledD a b : ℝ) : ℂ) := by
    intro h
    exact (led_real_data a b ha hb (ne_of_lt hab)).2.2.1 (Complex.ofReal_inj.mp h)
  have hquad2ne : xsC a b ^ 2 - ((ledC a b : ℝ) : ℂ) * xsC a b + 1 ≠ 0 := by
    have hsplit : xsC a b ^ 2 - ((ledC a b : ℝ) : ℂ) * xsC a b + 1
        = (((ledD a b : ℝ) : ℂ) - ((ledC a b : ℝ) : ℂ)) * xsC a b := by
      linear_combination hxsD
    rw [hsplit]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hLCne)) hxsC_ne0
  have h2 : (Q2x a b).eval (xsC a b) ≠ 0 := by
    rw [hQ2x_body]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_pow]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hxsC_ne_YC (sub_ne_zero.mpr hxsC_ne1)) hxsC_ne0)
        (by intro h; exact hxsC_nem1 (by linear_combination h)))
      hquad2ne
  -- part 3: `P1x x_s = Q2x x_s`
  have hderiv_Q4 : ((Q4x a b).map (algebraMap ℚ ℂ)).derivative
      = (2 * Polynomial.X - Polynomial.C (((ledC a b : ℝ) : ℂ)))
          * (Polynomial.X ^ 2 - Polynomial.C (((ledD a b : ℝ) : ℂ)) * Polynomial.X + 1)
        + (Polynomial.X ^ 2 - Polynomial.C (((ledC a b : ℝ) : ℂ)) * Polynomial.X + 1)
          * (2 * Polynomial.X - Polynomial.C (((ledD a b : ℝ) : ℂ))) := by
    rw [led_factor a b ha hb, Polynomial.derivative_mul, quad_deriv, quad_deriv]
  have hledD4map : (ledD4 a b).map (algebraMap ℚ ℂ)
      = ((Q4x a b).map (algebraMap ℚ ℂ)).derivative := by
    rw [← Q4x_derivative a b, Polynomial.derivative_map]
  have hD4ev : (ledD4 a b).eval₂ (algebraMap ℚ ℂ) (xsC a b)
      = (xsC a b - ((1 / xs a b : ℝ) : ℂ))
        * (xsC a b ^ 2 - ((ledC a b : ℝ) : ℂ) * xsC a b + 1) := by
    rw [Polynomial.eval₂_eq_eval_map, hledD4map, hderiv_Q4]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat]
    rw [hxsD, h2z]
    ring
  have h3 : (P1x a b).eval₂ (algebraMap ℚ ℂ) (xsC a b) = (Q2x a b).eval (xsC a b) := by
    rw [P1x_eq a b]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
    rw [hQ4, hD4ev]
    rw [hQ2x_body]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_pow]
    ring
  -- part 4: the divisibility
  have heval0 : ((P1x a b).map (algebraMap ℚ ℂ)
      - Polynomial.C ((Q2x a b).eval (xsC a b))).eval (xsC a b) = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map, h3, sub_self]
  have h4 : (Polynomial.X - Polynomial.C (xsC a b))
      ∣ ((P1x a b).map (algebraMap ℚ ℂ) - Polynomial.C ((Q2x a b).eval (xsC a b))) :=
    (Polynomial.dvd_iff_isRoot (a := xsC a b)).mpr (Polynomial.IsRoot.def.mpr heval0)
  obtain ⟨S, hS⟩ := h4
  exact ⟨h1, h2, h3, S, hS⟩

end

end Work.C17f
