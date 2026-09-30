import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Log.log_mod_decr_x_low
import Submission.Commons.Analysis.SpecialFunctions.Log.half_curve_log_le
import Submission.Commons.Analysis.SpecialFunctions.Log.log_strip_large_x_small_t
import Submission.Commons.Analysis.SpecialFunctions.Log.log_strip_quad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real ComplexConjugate
open Commons.Analysis.SpecialFunctions.Log
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-!
# The strip bound `‖log z‖ + (1/2)·‖z⁻¹‖ ≤ log (2 + |y|) + 3/2`

For `z = x + i·y` with `1/2 ≤ x ≤ 8`, we prove
`‖log z‖ + (1/2)·‖z⁻¹‖ ≤ log (2 + |y|) + 3/2`.  All real-inequality content is delegated
to the elementary lemmas in `Commons.Analysis.SpecialFunctions.Log` (`log_mod_decr_x_low`,
`half_curve_log_le`, `log_strip_large_x_small_t`, `log_strip_quad`); this file supplies the
complex-analysis bridge (exact modulus formula of the complex logarithm on a right
half-plane, conjugation symmetry in `y`) and the case analysis.
-/

namespace LogStrip

/-- `‖z‖ = √(x²+y²)` for `z = x + y·I`. -/
lemma norm_add_I_eq_sqrt (x y : ℝ) (hxy : 0 < x ^ 2 + y ^ 2) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  have h2 : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = Real.sqrt (x ^ 2 + y ^ 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (le_of_lt hxy)]
    simp
    ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h2) with h1 | h2
  · exact h1
  · have hsqrt : Real.sqrt (x ^ 2 + y ^ 2) > 0 := Real.sqrt_pos.2 hxy
    have hnz : 0 ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := norm_nonneg _
    linarith

/-- Real part of the complex logarithm at `x + y·I`: `(1/2)·log(x²+y²)`. -/
lemma log_re_add_I (x y : ℝ) (hxy : 0 < x ^ 2 + y ^ 2) :
    (Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) := by
  rw [Complex.log_re]
  rw [norm_add_I_eq_sqrt x y hxy]
  rw [Real.log_sqrt (le_of_lt hxy)]
  ring

/-- `√(x²+y²) = x·√(1+(y/x)²)` for `0 < x`. -/
lemma sqrt_sq_add_sq_eq_mul_sqrt_one (x y : ℝ) (hx : 0 < x) :
    Real.sqrt (x ^ 2 + y ^ 2) = x * Real.sqrt (1 + (y / x) ^ 2) := by
  have hfac : x ^ 2 + y ^ 2 = x ^ 2 * (1 + (y / x) ^ 2) := by
    field_simp [ne_of_gt hx]
  rw [hfac, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hx)]

/-- `y/√(x²+y²) = (y/x)/√(1+(y/x)²)` for `0 < x`. -/
lemma div_sqrt_eq (x y : ℝ) (hx : 0 < x) :
    y / Real.sqrt (x ^ 2 + y ^ 2) = (y / x) / Real.sqrt (1 + (y / x) ^ 2) := by
  rw [sqrt_sq_add_sq_eq_mul_sqrt_one x y hx]
  field_simp [ne_of_gt hx]

/-- For `0 < x` the argument of `x + y·I` is `arctan (y/x)`. -/
lemma arg_add_I_eq_arctan (x y : ℝ) (hx : 0 < x) :
    ((x : ℂ) + (y : ℂ) * Complex.I).arg = Real.arctan (y / x) := by
  have harg0 : ((x : ℂ) + (y : ℂ) * Complex.I).arg =
      Real.arcsin (y / ‖(x : ℂ) + (y : ℂ) * Complex.I‖) := by
    have hrepos : 0 ≤ ((x : ℂ) + (y : ℂ) * Complex.I).re := by
      rw [Complex.add_re]
      simp
      exact le_of_lt hx
    simpa using Complex.arg_of_re_nonneg hrepos
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hsqrt : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) :=
    norm_add_I_eq_sqrt x y hxy
  rw [hsqrt] at harg0
  have hdiv : y / Real.sqrt (x ^ 2 + y ^ 2) = (y / x) / Real.sqrt (1 + (y / x) ^ 2) :=
    div_sqrt_eq x y hx
  rw [hdiv] at harg0
  rw [harg0]
  exact (Real.arctan_eq_arcsin (y / x)).symm

/-- Exact modulus formula for the complex logarithm on the right half-plane:
`‖log (x+y·I)‖ = √(((1/2)·log(x²+y²))² + (arctan (y/x))²)`. -/
lemma norm_log_add_I_eq (x y : ℝ) (hx : 0 < x) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
      Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 + (Real.arctan (y / x)) ^ 2) := by
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hs : Complex.normSq (Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)) =
      (((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 + (Real.arctan (y / x)) ^ 2 := by
    rw [Complex.normSq_apply, log_re_add_I x y hxy, Complex.log_im,
      arg_add_I_eq_arctan x y hx]
    ring
  have h1 : ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 =
      Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 + (Real.arctan (y / x)) ^ 2) ^ 2 := by
    rw [Complex.sq_norm, hs, Real.sq_sqrt]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt : 0 ≤ Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 +
      (Real.arctan (y / x)) ^ 2) := Real.sqrt_nonneg _
  have hnz : 0 ≤ ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ := norm_nonneg _
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h1) with h1 | h2
  · exact h1
  · have hs0 : Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 +
        (Real.arctan (y / x)) ^ 2) ≤ 0 := by nlinarith [h2, hnz]
    have hs0' : Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 +
        (Real.arctan (y / x)) ^ 2) = 0 := by linarith
    have hlog0 : ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ = 0 := by nlinarith [h2, hs0']
    rw [hs0']
    exact hlog0

/-- `arctan u ≤ u` for `0 ≤ u`. -/
lemma arctan_le_self (u : ℝ) (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  by_cases hu0 : u = 0
  · subst u
    simp
  · have hd : ∀ a : ℝ, HasDerivAt (fun z : ℝ => z - Real.arctan z) (1 - 1 / (1 + a ^ 2)) a := by
      intro a
      have h1 : HasDerivAt (fun z : ℝ => z) 1 a := hasDerivAt_id a
      have h2 : HasDerivAt (fun z : ℝ => Real.arctan z) (1 / (1 + a ^ 2)) a := by
        simpa using Real.hasDerivAt_arctan a
      exact h1.sub h2
    have hcont : ContinuousOn (fun z : ℝ => z - Real.arctan z) (Set.Icc 0 u) := by
      intro a ha
      exact (hd a).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun z : ℝ => z - Real.arctan z) (interior (Set.Icc 0 u)) := by
      intro a ha
      exact (hd a).differentiableAt.differentiableWithinAt
    have hnn : ∀ a ∈ interior (Set.Icc 0 u), 0 ≤ deriv (fun z : ℝ => z - Real.arctan z) a := by
      intro a ha
      rw [(hd a).deriv]
      have hapos : 0 < a := by
        have : a ∈ Set.Ioo 0 u := by simpa [interior_Icc] using ha
        exact this.1
      have hf : 1 - 1 / (1 + a ^ 2) = a ^ 2 / (1 + a ^ 2) := by
        field_simp [show 1 + a ^ 2 ≠ 0 by positivity]
        ring
      rw [hf]
      exact div_nonneg (sq_nonneg a) (by positivity)
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hcont hdiff hnn
    have h0m : (0 : ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
    have hum : u ∈ Set.Icc 0 u := ⟨hu, le_rfl⟩
    have hle := hmono h0m hum hu
    simpa using hle

/-- `ln(1+u²) ≤ u²`. -/
lemma log_one_add_sq_le_sq (u : ℝ) : Real.log (1 + u ^ 2) ≤ u ^ 2 := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + u ^ 2 by positivity)
  nlinarith

/-- Quadratic refinement of the square root: `√(a²+b²) ≤ a + b²/(2a)` for `0 < a`. -/
lemma sqrt_sq_add_sq_le (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b ^ 2 / (2 * a) := by
  have hsq : a ^ 2 + b ^ 2 ≤ (a + b ^ 2 / (2 * a)) ^ 2 := by
    have hmain : (a + b ^ 2 / (2 * a)) ^ 2 - (a ^ 2 + b ^ 2) = (b ^ 2) ^ 2 / (4 * a ^ 2) := by
      field_simp [ne_of_gt ha]
      ring
    have hnon : 0 ≤ (b ^ 2) ^ 2 / (4 * a ^ 2) := by positivity
    nlinarith
  calc
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b ^ 2 / (2 * a)) ^ 2) := by
      rw [Real.le_sqrt (Real.sqrt_nonneg _) (by positivity)]
      rw [Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
      exact hsq
    _ = a + b ^ 2 / (2 * a) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity

/-- `ln(√(x²+y²)) = (1/2)·log(x²+y²)` for `0 < x²+y²`. -/
lemma log_sqrt_sq_add (x y : ℝ) (hxy : 0 < x ^ 2 + y ^ 2) :
    Real.log (Real.sqrt (x ^ 2 + y ^ 2)) = ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) := by
  rw [Real.log_sqrt (le_of_lt hxy)]
  ring

/-- `√(a²+b²) ≤ a + b` for nonnegative `a`,`b`. -/
lemma sqrt_sq_add_sq_le_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  have hsq : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hnon : 0 ≤ a + b := by linarith
  calc
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) := by
      rw [Real.le_sqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ (a + b) ^ 2)]
      rw [Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
      exact hsq
    _ = a + b := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnon]

/-- `‖log (x+y·I)‖ ≤ log x + u + u²/2` with `u = y/x`, for `1 ≤ x`, `0 ≤ y`. -/
lemma norm_log_le_chain (x y : ℝ) (hx1 : 1 ≤ x) (hy : 0 ≤ y) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.log x + y / x + (y / x) ^ 2 / 2 := by
  have hxpos : 0 < x := by linarith
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hA0 : 0 ≤ ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) := by
    have hxy1 : 1 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, hx1]
    have hlogge : 0 ≤ Real.log (x ^ 2 + y ^ 2) := Real.log_nonneg hxy1
    positivity
  have hB0 : 0 ≤ Real.arctan (y / x) :=
    (Real.arctan_nonneg).2 (div_nonneg hy (le_of_lt hxpos))
  have hlog := norm_log_add_I_eq x y hxpos
  have hsqrt : Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 +
      (Real.arctan (y / x)) ^ 2) ≤ ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) +
        Real.arctan (y / x) := by
    simpa using sqrt_sq_add_sq_le_add (((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2))
      (Real.arctan (y / x)) hA0 hB0
  have hlogle : ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) ≤ Real.log x + (y / x) ^ 2 / 2 := by
    have hxy' : Real.sqrt (x ^ 2 + y ^ 2) = x * Real.sqrt (1 + (y / x) ^ 2) :=
      sqrt_sq_add_sq_eq_mul_sqrt_one x y hxpos
    have hlogxy : ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) =
        Real.log (x * Real.sqrt (1 + (y / x) ^ 2)) := by
      rw [← log_sqrt_sq_add x y hxy]
      exact congrArg Real.log hxy'
    calc
      ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)
          = Real.log (x * Real.sqrt (1 + (y / x) ^ 2)) := hlogxy
      _ = Real.log x + Real.log (Real.sqrt (1 + (y / x) ^ 2)) := by
          rw [Real.log_mul (ne_of_gt hxpos) (ne_of_gt
            (Real.sqrt_pos.2 (by positivity : 0 < 1 + (y / x) ^ 2)))]
      _ = Real.log x + ((1 : ℝ) / 2) * Real.log (1 + (y / x) ^ 2) := by
          rw [Real.log_sqrt (by positivity : 0 ≤ 1 + (y / x) ^ 2)]
          ring
      _ ≤ Real.log x + (y / x) ^ 2 / 2 := by
          have hsq := log_one_add_sq_le_sq (y / x)
          linarith
  calc
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖
        = Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2)) ^ 2 +
            (Real.arctan (y / x)) ^ 2) := hlog
    _ ≤ ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) + Real.arctan (y / x) := hsqrt
    _ ≤ Real.log x + y / x + (y / x) ^ 2 / 2 := by
        have harctle : Real.arctan (y / x) ≤ y / x :=
          arctan_le_self (y / x) (div_nonneg hy (le_of_lt hxpos))
        linarith

/-- `(1/2)·‖(x+y·I)⁻¹‖ ≤ 1/(2x)` for `0 < x`. -/
lemma inv_le (x y : ℝ) (hx : 0 < x) :
    ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤ (1 : ℝ) / (2 * x) := by
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hnorm := norm_add_I_eq_sqrt x y hxy
  have hxeq : Real.sqrt (x ^ 2) = x := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hx)]
  have hle : x ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    have hsqle : x ^ 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
    have hsqrt : Real.sqrt (x ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_le_sqrt hsqle
    exact (le_of_eq hxeq.symm).trans hsqrt
  have hpos : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.2 hxy
  have hinv : (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ ≤ x⁻¹ := by
    exact (inv_le_inv₀ hpos hx).mpr hle
  calc
    ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
        = ((1 : ℝ) / 2) * ‖((x : ℂ) + (y : ℂ) * Complex.I)‖⁻¹ := by rw [norm_inv]
    _ = ((1 : ℝ) / 2) * (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ := by rw [hnorm]
    _ ≤ ((1 : ℝ) / 2) * x⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = (1 : ℝ) / (2 * x) := by
        field_simp [ne_of_gt hx]

/-- Main strip bound for `y ≥ 0`, case `x ≤ 1` (reduces to the curve `x = 1/2`). -/
lemma nonneg_case_low_x (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hxle1 : x ≤ 1) (hy : 0 ≤ y) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      Real.log (2 + y) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hdec' : ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.sqrt ((((1 : ℝ) / 2) * Real.log (y ^ 2 + (1 : ℝ) / 4)) ^ 2 +
        (Real.arctan (2 * y)) ^ 2) := by
    have hA := norm_log_add_I_eq x y hxpos
    have hdec := log_mod_decr_x_low x y hx1 hxle1 hy
    -- hdec compares √(x-part) with √(((1/2)·log(1/4+y²))² + atan(2y)²); normalise log arg order
    have harg : (1 : ℝ) / 4 + y ^ 2 = y ^ 2 + (1 : ℝ) / 4 := by ring
    rw [harg] at hdec
    rw [hA]
    exact hdec
  have hinv' : ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      ((1 : ℝ) / 2) * (Real.sqrt (y ^ 2 + (1 : ℝ) / 4))⁻¹ := by
    have hnorm := norm_add_I_eq_sqrt x y hxy
    have hx2sq : (1 : ℝ) / 4 ≤ x ^ 2 := by
      have hm := mul_le_mul hx1 hx1 (by norm_num) (le_of_lt hxpos)
      norm_num at hm
      simpa [pow_two] using hm
    have hsq_le : y ^ 2 + (1 : ℝ) / 4 ≤ x ^ 2 + y ^ 2 := by nlinarith
    have hsqrt_le : Real.sqrt (y ^ 2 + (1 : ℝ) / 4) ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
      Real.sqrt_le_sqrt hsq_le
    have hpos1 : 0 < Real.sqrt (y ^ 2 + (1 : ℝ) / 4) :=
      Real.sqrt_pos.2 (by positivity : 0 < y ^ 2 + (1 : ℝ) / 4)
    have hpos2 : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.2 hxy
    have hinv : (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ ≤ (Real.sqrt (y ^ 2 + (1 : ℝ) / 4))⁻¹ :=
      (inv_le_inv₀ hpos2 hpos1).mpr hsqrt_le
    calc
      ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
          = ((1 : ℝ) / 2) * (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ := by
            rw [norm_inv, hnorm]
      _ ≤ ((1 : ℝ) / 2) * (Real.sqrt (y ^ 2 + (1 : ℝ) / 4))⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hc := half_curve_log_le y hy
  calc
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
        ≤ Real.sqrt ((((1 : ℝ) / 2) * Real.log (y ^ 2 + (1 : ℝ) / 4)) ^ 2 +
            (Real.arctan (2 * y)) ^ 2) +
            ((1 : ℝ) / 2) * (Real.sqrt (y ^ 2 + (1 : ℝ) / 4))⁻¹ := by
            exact add_le_add hdec' hinv'
    _ ≤ Real.log (2 + y) + (3 : ℝ) / 2 := hc

/-- Conjugation: `x + y·I = conj (x + (−y)·I)`. -/
lemma z_conj_eq (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I) = conj ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp

/-- The norm of the complex logarithm is even in the imaginary part (right half-plane):
`‖log (x + y·I)‖ = ‖log (x + (−y)·I)‖`. -/
lemma norm_log_even_in_y (x y : ℝ) (hx : 0 < x) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
      ‖Complex.log ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖ := by
  let w : ℂ := (x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I
  have hz : ((x : ℂ) + (y : ℂ) * Complex.I) = conj w := by
    rw [z_conj_eq]
  rw [hz]
  have harg : w.arg ≠ Real.pi := by
    have hwre : 0 < w.re := by
      simp [w]
      exact hx
    have habs : |w.arg| < Real.pi / 2 := by
      rw [Complex.abs_arg_lt_pi_div_two_iff]
      exact Or.inl hwre
    have hlt : Real.pi / 2 < Real.pi := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
    intro h
    have hargle : w.arg ≤ Real.pi / 2 := le_trans (le_abs_self _) (le_of_lt habs)
    linarith
  rw [Complex.log_conj w harg]
  simp [w]

/-- The norm of the inverse is even in the imaginary part (right half-plane). -/
lemma norm_inv_even_in_y (x y : ℝ) (hx : 0 < x) :
    ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ =
      ‖(((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)⁻¹)‖ := by
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hxy2 : 0 < x ^ 2 + (-y) ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  rw [norm_inv, norm_inv]
  congr 1
  rw [norm_add_I_eq_sqrt x y hxy, norm_add_I_eq_sqrt x (-y) hxy2]
  congr 2
  ring

/-- Case `1 ≤ x ≤ 8`, `y ≥ 1`: quadratic refinement plus `log_strip_quad`. -/
lemma quad_case (x y : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (hy : 0 ≤ y) (hy1 : 1 ≤ y) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      Real.log (2 + y) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith
  have hlog := norm_log_add_I_eq x y hxpos
  have hA : ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) =
      Real.log (Real.sqrt (x ^ 2 + y ^ 2)) := by
    exact (log_sqrt_sq_add x y hxy).symm
  have hApos : 0 < ((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2) := by
    have hgt : 1 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y, hx1, hy1]
    have hlogp : 0 < Real.log (x ^ 2 + y ^ 2) := Real.log_pos hgt
    positivity
  have hq1 : ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.log (Real.sqrt (x ^ 2 + y ^ 2)) +
        (Real.arctan (y / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + y ^ 2))) := by
    rw [hlog]
    rw [hA]
    have hq := sqrt_sq_add_sq_le (((1 : ℝ) / 2) * Real.log (x ^ 2 + y ^ 2))
      (Real.arctan (y / x)) hApos
    rw [hA] at hq
    exact hq
  have hq2 : ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ =
      (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + y ^ 2)) := by
    have hsqrtpos : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.2 hxy
    rw [norm_inv, norm_add_I_eq_sqrt x y hxy]
    field_simp [ne_of_gt hsqrtpos]
  have hq := log_strip_quad x y hx1 hx2 hy1
  calc
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
        ≤ (Real.log (Real.sqrt (x ^ 2 + y ^ 2)) +
            (Real.arctan (y / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + y ^ 2)))) +
            (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + y ^ 2)) := by
            exact add_le_add hq1 (le_of_eq hq2)
    _ ≤ Real.log (2 + y) + (3 : ℝ) / 2 := hq

/-- Main strip bound for `y ≥ 0`. -/
lemma log_z_half_inv_strip_le_nonneg (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 8)
    (hy : 0 ≤ y) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      Real.log (2 + y) + (3 : ℝ) / 2 := by
  by_cases hxle1 : x ≤ 1
  · exact nonneg_case_low_x x y hx1 hxle1 hy
  · have hxge1 : 1 ≤ x := by linarith
    by_cases hyle1 : y ≤ 1
    · -- x in [1,8], y in [0,1]: chain via log_strip_large_x_small_t
      have h1 := norm_log_le_chain x y hxge1 hy
      have h2 := inv_le x y (by linarith)
      have h3 := log_strip_large_x_small_t x y hxge1 hx2 hy hyle1
      calc
        ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
            ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
            ≤ (Real.log x + y / x + (y / x) ^ 2 / 2) + (1 : ℝ) / (2 * x) := add_le_add h1 h2
        _ ≤ Real.log (2 + y) + (3 : ℝ) / 2 := h3
    · -- x in [1,8], y ≥ 1: quadratic bound + log_strip_quad
      exact quad_case x y hxge1 hx2 hy (by linarith)

/-- Conjugation symmetry gives the bound for arbitrary real `y`. -/
lemma log_z_half_inv_strip_le_all_y (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 8) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      Real.log (2 + |y|) + (3 : ℝ) / 2 := by
  by_cases hy : 0 ≤ y
  · have h := log_z_half_inv_strip_le_nonneg x y hx1 hx2 hy
    rw [abs_of_nonneg hy]
    exact h
  · have h' : 0 ≤ -y := by linarith
    have h := log_z_half_inv_strip_le_nonneg x (-y) hx1 hx2 h'
    have hlog : ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
        ‖Complex.log ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖ :=
      norm_log_even_in_y x y (by linarith : 0 < x)
    have hinv : ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ =
        ‖(((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)⁻¹)‖ :=
      norm_inv_even_in_y x y (by linarith : 0 < x)
    rw [hlog, hinv]
    have habs : |y| = -y := abs_of_nonpos (le_of_not_ge hy)
    rw [habs]
    exact h

end LogStrip

/-- **Strip bound for the logarithm and the inverse modulus**:
`‖log (x + y·I)‖ + (1/2)·‖(x + y·I)⁻¹‖ ≤ log (2 + |y|) + 3/2` on the strip
`1/2 ≤ x ≤ 8`. -/
theorem log_z_half_inv_strip_le (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 8) :
    ‖Complex.log ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ((1 : ℝ) / 2) * ‖(((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤
      Real.log (2 + |y|) + (3 : ℝ) / 2 := by
  exact LogStrip.log_z_half_inv_strip_le_all_y x y hx1 hx2

end Commons.Analysis.SpecialFunctions.Gamma
