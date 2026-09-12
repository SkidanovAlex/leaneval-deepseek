import Mathlib

/-! Numerical bounds for sinc integrals behind Lemma si.

Target (true values in parentheses): `∫_0^{2π} sinc ≥ 4/3` (≈1.418),
`∫_0^{π} sinc ≤ 2` (≈1.852), and `∫_π^{2π} sinc ≥ -1` (≈-0.434).

Approach: elementary calculus.  We first develop (Part A) the basic
interval-integral facts for `sin`/`cos`, then (Part B) prove global
polynomial partial-sum bounds for `sin`/`cos` (a zig-zag of
"integrate a bound" steps), then (Part C) split the sinc integrals into
pieces with rational endpoints and bound each piece. -/

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Set

set_option autoImplicit false

namespace Submission
namespace SincNum

/-! ## Part A. Basic calculus helpers -/

/-- `∫_0^x sin = 1 - cos x` -/
lemma integral_sin_zero_x (x : ℝ) : ∫ t in (0 : ℝ)..x, Real.sin t = 1 - Real.cos x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (-Real.cos) (Real.sin y) y := by
    intro y hy
    exact ((Real.hasDerivAt_cos y).neg).congr_deriv (by simp)
  have hint : IntervalIntegrable (fun u : ℝ => Real.sin u) volume 0 x := by
    exact (Real.continuous_sin).intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hF]
  simp [Real.cos_zero]
  ring

/-- `∫_a^b sin = cos a - cos b` -/
lemma integral_sin_a_b (a b : ℝ) : ∫ x in a..b, Real.sin x = Real.cos a - Real.cos b := by
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt (-Real.cos) (Real.sin y) y := by
    intro y hy
    exact ((Real.hasDerivAt_cos y).neg).congr_deriv (by simp)
  have hint : IntervalIntegrable (fun u : ℝ => Real.sin u) volume a b := by
    exact (Real.continuous_sin).intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hF]
  dsimp
  ring

/-- `sin x = ∫_0^x cos` -/
lemma sin_eq_int_cos (x : ℝ) : Real.sin x = ∫ t in (0 : ℝ)..x, Real.cos t := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt Real.sin (Real.cos y) y := by
    intro y hy
    exact Real.hasDerivAt_sin y
  have hint : IntervalIntegrable (fun u : ℝ => Real.cos u) volume 0 x := by
    exact (Real.continuous_cos).intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hF]
  simp [Real.sin_zero]

/-- `cos x = 1 - ∫_0^x sin` -/
lemma cos_eq_one_sub_int_sin (x : ℝ) : Real.cos x = 1 - ∫ t in (0 : ℝ)..x, Real.sin t := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt Real.cos (-(Real.sin y)) y := by
    intro y hy
    exact Real.hasDerivAt_cos y
  have hint : IntervalIntegrable (fun u : ℝ => -(Real.sin u)) volume 0 x := by
    exact (Real.continuous_sin).neg.intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hneg : ∫ t in (0:ℝ)..x, -(Real.sin t) = -∫ t in (0:ℝ)..x, Real.sin t := by
    exact intervalIntegral.integral_neg
  rw [hneg] at hF
  -- hF : -(∫ sin) = cos x - cos 0
  have hc0 : Real.cos 0 = 1 := by simp
  rw [hc0] at hF
  linarith

/-- FTC for `∫_0^x L = A x - A 0` given a derivative on `[0,x]`. -/
lemma int_zero_eq_sub {x : ℝ} {L A : ℝ → ℝ} (hx : 0 ≤ x)
    (hcont : Continuous L)
    (hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt A (L y) y) :
    ∫ t in (0 : ℝ)..x, L t = A x - A 0 := by
  have hint : IntervalIntegrable L volume 0 x := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-! Four "lifting" steps: an integral bound plus an antiderivative gives a new bound. -/

lemma sin_ge_of_cos_ge {x : ℝ} (hx : 0 ≤ x) {L A : ℝ → ℝ}
    (hpt : ∀ t, 0 ≤ t → L t ≤ Real.cos t)
    (hcont : Continuous L)
    (hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt A (L y) y) :
    A x - A 0 ≤ Real.sin x := by
  have hintC : IntervalIntegrable (fun t : ℝ => Real.cos t) volume 0 x :=
    (Real.continuous_cos).intervalIntegrable _ _
  have hintL : IntervalIntegrable L volume 0 x := hcont.intervalIntegrable _ _
  have hmono : (∫ t in (0:ℝ)..x, L t) ≤ ∫ t in (0:ℝ)..x, Real.cos t := by
    refine intervalIntegral.integral_mono_on hx hintL hintC ?_
    intro t ht
    exact hpt t ht.1
  have hftc : ∫ t in (0:ℝ)..x, L t = A x - A 0 := int_zero_eq_sub hx hcont hderiv
  rw [sin_eq_int_cos x]
  linarith

lemma sin_le_of_cos_le {x : ℝ} (hx : 0 ≤ x) {U A : ℝ → ℝ}
    (hpt : ∀ t, 0 ≤ t → Real.cos t ≤ U t)
    (hcont : Continuous U)
    (hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt A (U y) y) :
    Real.sin x ≤ A x - A 0 := by
  have hintC : IntervalIntegrable (fun t : ℝ => Real.cos t) volume 0 x :=
    (Real.continuous_cos).intervalIntegrable _ _
  have hintU : IntervalIntegrable U volume 0 x := hcont.intervalIntegrable _ _
  have hmono : (∫ t in (0:ℝ)..x, Real.cos t) ≤ ∫ t in (0:ℝ)..x, U t := by
    refine intervalIntegral.integral_mono_on hx hintC hintU ?_
    intro t ht
    exact hpt t ht.1
  have hftc : ∫ t in (0:ℝ)..x, U t = A x - A 0 := int_zero_eq_sub hx hcont hderiv
  rw [sin_eq_int_cos x]
  linarith

lemma cos_le_of_sin_ge {x : ℝ} (hx : 0 ≤ x) {L A : ℝ → ℝ}
    (hpt : ∀ t, 0 ≤ t → L t ≤ Real.sin t)
    (hcont : Continuous L)
    (hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt A (L y) y) :
    Real.cos x ≤ 1 - (A x - A 0) := by
  have hintS : IntervalIntegrable (fun t : ℝ => Real.sin t) volume 0 x :=
    (Real.continuous_sin).intervalIntegrable _ _
  have hintL : IntervalIntegrable L volume 0 x := hcont.intervalIntegrable _ _
  have hmono : (∫ t in (0:ℝ)..x, L t) ≤ ∫ t in (0:ℝ)..x, Real.sin t := by
    refine intervalIntegral.integral_mono_on hx hintL hintS ?_
    intro t ht
    exact hpt t ht.1
  have hftc : ∫ t in (0:ℝ)..x, L t = A x - A 0 := int_zero_eq_sub hx hcont hderiv
  rw [cos_eq_one_sub_int_sin x]
  linarith

lemma cos_ge_of_sin_le {x : ℝ} (hx : 0 ≤ x) {U A : ℝ → ℝ}
    (hpt : ∀ t, 0 ≤ t → Real.sin t ≤ U t)
    (hcont : Continuous U)
    (hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt A (U y) y) :
    1 - (A x - A 0) ≤ Real.cos x := by
  have hintS : IntervalIntegrable (fun t : ℝ => Real.sin t) volume 0 x :=
    (Real.continuous_sin).intervalIntegrable _ _
  have hintU : IntervalIntegrable U volume 0 x := hcont.intervalIntegrable _ _
  have hmono : (∫ t in (0:ℝ)..x, Real.sin t) ≤ ∫ t in (0:ℝ)..x, U t := by
    refine intervalIntegral.integral_mono_on hx hintS hintU ?_
    intro t ht
    exact hpt t ht.1
  have hftc : ∫ t in (0:ℝ)..x, U t = A x - A 0 := int_zero_eq_sub hx hcont hderiv
  rw [cos_eq_one_sub_int_sin x]
  linarith

/-! ## Part B. Polynomial partial-sum bounds for `sin` and `cos`.

The lemmas below state (global, for every `x ≥ 0`) that the `sin`/`cos`
Taylor partial sums bracket the functions.  They are obtained by a zig-zag
of "integrate a bound" steps (`sin = ∫ cos`, `cos = 1 - ∫ sin`), starting
from the elementary bounds `sin x ≤ x`, `sin x ≥ x - x³/6`,
`cos x ≤ 1`, `cos x ≥ 1 - x²/2`. -/

/-- Base: `cos x ≤ 1`. -/
lemma cos_le_0 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 := Real.cos_le_one x

/-- Base: `cos x ≥ 1 - x²/2`. -/
lemma cos_ge_0 (x : ℝ) (hx : 0 ≤ x) : 1 - x^2/2 ≤ Real.cos x := by
  exact Real.one_sub_sq_div_two_le_cos (x := x)

/-- Base: `sin x ≤ x`. -/
lemma sin_le_0 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x := Real.sin_le hx

/-- Base: `sin x ≥ x - x³/6`. -/
lemma sin_ge_0 (x : ℝ) (hx : 0 ≤ x) : x - x^3/6 ≤ Real.sin x := by
  exact Real.sin_ge_sub_cube hx

/-- chain claim `cos_le_1` -/
lemma cos_le_1 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x^2/2 + x^4/24 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24) (y - y^3/6) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24) (2 * y / 2 - 4 * y^3 / 24) y := (h0).sub h1
    convert hd using 1 <;> ring
  have h := cos_le_of_sin_ge hx (fun t ht => sin_ge_0 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_le_1` -/
lemma sin_le_1 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x^3/6 + x^5/120 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120) (1 - y^2/2 + y^4/24) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120) (1 - 3 * y^2 / 6 + 5 * y^4 / 120) y := ((h0).sub h1).add h2
    convert hd using 1 <;> ring
  have h := sin_le_of_cos_le hx (fun t ht => cos_le_1 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_ge_1` -/
lemma cos_ge_1 (x : ℝ) (hx : 0 ≤ x) : 1 - x^2/2 + x^4/24 - x^6/720 ≤ Real.cos x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720) (y - y^3/6 + y^5/120) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720) y := ((h0).sub h1).add h2
    convert hd using 1 <;> ring
  have h := cos_ge_of_sin_le hx (fun t ht => sin_le_1 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_ge_1` -/
lemma sin_ge_1 (x : ℝ) (hx : 0 ≤ x) : x - x^3/6 + x^5/120 - x^7/5040 ≤ Real.sin x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040) (1 - y^2/2 + y^4/24 - y^6/720) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040) y := (((h0).sub h1).add h2).sub h3
    convert hd using 1 <;> ring
  have h := sin_ge_of_cos_ge hx (fun t ht => cos_ge_1 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_le_2` -/
lemma cos_le_2 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320) (y - y^3/6 + y^5/120 - y^7/5040) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320) y := (((h0).sub h1).add h2).sub h3
    convert hd using 1 <;> ring
  have h := cos_le_of_sin_ge hx (fun t ht => sin_ge_1 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_le_2` -/
lemma sin_le_2 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880) y := ((((h0).sub h1).add h2).sub h3).add h4
    convert hd using 1 <;> ring
  have h := sin_le_of_cos_le hx (fun t ht => cos_le_2 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_ge_2` -/
lemma cos_ge_2 (x : ℝ) (hx : 0 ≤ x) : 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 ≤ Real.cos x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800) (y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have h4 : HasDerivAt (fun u : ℝ => u^10/3628800) (10 * y^9 / 3628800) y := by
      simpa using (hasDerivAt_pow 10 y).div_const 3628800
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320 + 10 * y^9 / 3628800) y := ((((h0).sub h1).add h2).sub h3).add h4
    convert hd using 1 <;> ring
  have h := cos_ge_of_sin_le hx (fun t ht => sin_le_2 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_ge_2` -/
lemma sin_ge_2 (x : ℝ) (hx : 0 ≤ x) : x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 ≤ Real.sin x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have h5 : HasDerivAt (fun u : ℝ => u^11/39916800) (11 * y^10 / 39916800) y := by
      simpa using (hasDerivAt_pow 11 y).div_const 39916800
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880 - 11 * y^10 / 39916800) y := (((((h0).sub h1).add h2).sub h3).add h4).sub h5
    convert hd using 1 <;> ring
  have h := sin_ge_of_cos_ge hx (fun t ht => cos_ge_2 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_le_3` -/
lemma cos_le_3 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 + x^12/479001600 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600) (y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have h4 : HasDerivAt (fun u : ℝ => u^10/3628800) (10 * y^9 / 3628800) y := by
      simpa using (hasDerivAt_pow 10 y).div_const 3628800
    have h5 : HasDerivAt (fun u : ℝ => u^12/479001600) (12 * y^11 / 479001600) y := by
      simpa using (hasDerivAt_pow 12 y).div_const 479001600
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320 + 10 * y^9 / 3628800 - 12 * y^11 / 479001600) y := (((((h0).sub h1).add h2).sub h3).add h4).sub h5
    convert hd using 1 <;> ring
  have h := cos_le_of_sin_ge hx (fun t ht => sin_ge_2 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_le_3` -/
lemma sin_le_3 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 + x^13/6227020800 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have h5 : HasDerivAt (fun u : ℝ => u^11/39916800) (11 * y^10 / 39916800) y := by
      simpa using (hasDerivAt_pow 11 y).div_const 39916800
    have h6 : HasDerivAt (fun u : ℝ => u^13/6227020800) (13 * y^12 / 6227020800) y := by
      simpa using (hasDerivAt_pow 13 y).div_const 6227020800
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880 - 11 * y^10 / 39916800 + 13 * y^12 / 6227020800) y := ((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6
    convert hd using 1 <;> ring
  have h := sin_le_of_cos_le hx (fun t ht => cos_le_3 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800 + t^12/479001600)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_ge_3` -/
lemma cos_ge_3 (x : ℝ) (hx : 0 ≤ x) : 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 + x^12/479001600 - x^14/87178291200 ≤ Real.cos x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200) (y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800 + y^13/6227020800) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have h4 : HasDerivAt (fun u : ℝ => u^10/3628800) (10 * y^9 / 3628800) y := by
      simpa using (hasDerivAt_pow 10 y).div_const 3628800
    have h5 : HasDerivAt (fun u : ℝ => u^12/479001600) (12 * y^11 / 479001600) y := by
      simpa using (hasDerivAt_pow 12 y).div_const 479001600
    have h6 : HasDerivAt (fun u : ℝ => u^14/87178291200) (14 * y^13 / 87178291200) y := by
      simpa using (hasDerivAt_pow 14 y).div_const 87178291200
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320 + 10 * y^9 / 3628800 - 12 * y^11 / 479001600 + 14 * y^13 / 87178291200) y := ((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6
    convert hd using 1 <;> ring
  have h := cos_ge_of_sin_le hx (fun t ht => sin_le_3 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800 + t^13/6227020800)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_ge_3` -/
lemma sin_ge_3 (x : ℝ) (hx : 0 ≤ x) : x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 + x^13/6227020800 - x^15/1307674368000 ≤ Real.sin x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600 - y^14/87178291200) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have h5 : HasDerivAt (fun u : ℝ => u^11/39916800) (11 * y^10 / 39916800) y := by
      simpa using (hasDerivAt_pow 11 y).div_const 39916800
    have h6 : HasDerivAt (fun u : ℝ => u^13/6227020800) (13 * y^12 / 6227020800) y := by
      simpa using (hasDerivAt_pow 13 y).div_const 6227020800
    have h7 : HasDerivAt (fun u : ℝ => u^15/1307674368000) (15 * y^14 / 1307674368000) y := by
      simpa using (hasDerivAt_pow 15 y).div_const 1307674368000
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880 - 11 * y^10 / 39916800 + 13 * y^12 / 6227020800 - 15 * y^14 / 1307674368000) y := (((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7
    convert hd using 1 <;> ring
  have h := sin_ge_of_cos_ge hx (fun t ht => cos_ge_3 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800 + t^12/479001600 - t^14/87178291200)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_le_4` -/
lemma cos_le_4 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 + x^12/479001600 - x^14/87178291200 + x^16/20922789888000 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200 - u^16/20922789888000) (y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800 + y^13/6227020800 - y^15/1307674368000) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have h4 : HasDerivAt (fun u : ℝ => u^10/3628800) (10 * y^9 / 3628800) y := by
      simpa using (hasDerivAt_pow 10 y).div_const 3628800
    have h5 : HasDerivAt (fun u : ℝ => u^12/479001600) (12 * y^11 / 479001600) y := by
      simpa using (hasDerivAt_pow 12 y).div_const 479001600
    have h6 : HasDerivAt (fun u : ℝ => u^14/87178291200) (14 * y^13 / 87178291200) y := by
      simpa using (hasDerivAt_pow 14 y).div_const 87178291200
    have h7 : HasDerivAt (fun u : ℝ => u^16/20922789888000) (16 * y^15 / 20922789888000) y := by
      simpa using (hasDerivAt_pow 16 y).div_const 20922789888000
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200 - u^16/20922789888000) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320 + 10 * y^9 / 3628800 - 12 * y^11 / 479001600 + 14 * y^13 / 87178291200 - 16 * y^15 / 20922789888000) y := (((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7
    convert hd using 1 <;> ring
  have h := cos_le_of_sin_ge hx (fun t ht => sin_ge_3 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800 + t^13/6227020800 - t^15/1307674368000)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_le_4` -/
lemma sin_le_4 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 + x^13/6227020800 - x^15/1307674368000 + x^17/355687428096000 := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000 + u^17/355687428096000) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600 - y^14/87178291200 + y^16/20922789888000) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have h5 : HasDerivAt (fun u : ℝ => u^11/39916800) (11 * y^10 / 39916800) y := by
      simpa using (hasDerivAt_pow 11 y).div_const 39916800
    have h6 : HasDerivAt (fun u : ℝ => u^13/6227020800) (13 * y^12 / 6227020800) y := by
      simpa using (hasDerivAt_pow 13 y).div_const 6227020800
    have h7 : HasDerivAt (fun u : ℝ => u^15/1307674368000) (15 * y^14 / 1307674368000) y := by
      simpa using (hasDerivAt_pow 15 y).div_const 1307674368000
    have h8 : HasDerivAt (fun u : ℝ => u^17/355687428096000) (17 * y^16 / 355687428096000) y := by
      simpa using (hasDerivAt_pow 17 y).div_const 355687428096000
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000 + u^17/355687428096000) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880 - 11 * y^10 / 39916800 + 13 * y^12 / 6227020800 - 15 * y^14 / 1307674368000 + 17 * y^16 / 355687428096000) y := ((((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7).add h8
    convert hd using 1 <;> ring
  have h := sin_le_of_cos_le hx (fun t ht => cos_le_4 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800 + t^12/479001600 - t^14/87178291200 + t^16/20922789888000)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `cos_ge_4` -/
lemma cos_ge_4 (x : ℝ) (hx : 0 ≤ x) : 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 + x^12/479001600 - x^14/87178291200 + x^16/20922789888000 - x^18/6402373705728000 ≤ Real.cos x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200 - u^16/20922789888000 + u^18/6402373705728000) (y - y^3/6 + y^5/120 - y^7/5040 + y^9/362880 - y^11/39916800 + y^13/6227020800 - y^15/1307674368000 + y^17/355687428096000) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u^2/2) (2 * y / 2) y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h1 : HasDerivAt (fun u : ℝ => u^4/24) (4 * y^3 / 24) y := by
      simpa using (hasDerivAt_pow 4 y).div_const 24
    have h2 : HasDerivAt (fun u : ℝ => u^6/720) (6 * y^5 / 720) y := by
      simpa using (hasDerivAt_pow 6 y).div_const 720
    have h3 : HasDerivAt (fun u : ℝ => u^8/40320) (8 * y^7 / 40320) y := by
      simpa using (hasDerivAt_pow 8 y).div_const 40320
    have h4 : HasDerivAt (fun u : ℝ => u^10/3628800) (10 * y^9 / 3628800) y := by
      simpa using (hasDerivAt_pow 10 y).div_const 3628800
    have h5 : HasDerivAt (fun u : ℝ => u^12/479001600) (12 * y^11 / 479001600) y := by
      simpa using (hasDerivAt_pow 12 y).div_const 479001600
    have h6 : HasDerivAt (fun u : ℝ => u^14/87178291200) (14 * y^13 / 87178291200) y := by
      simpa using (hasDerivAt_pow 14 y).div_const 87178291200
    have h7 : HasDerivAt (fun u : ℝ => u^16/20922789888000) (16 * y^15 / 20922789888000) y := by
      simpa using (hasDerivAt_pow 16 y).div_const 20922789888000
    have h8 : HasDerivAt (fun u : ℝ => u^18/6402373705728000) (18 * y^17 / 6402373705728000) y := by
      simpa using (hasDerivAt_pow 18 y).div_const 6402373705728000
    have hd : HasDerivAt (fun u : ℝ => u^2/2 - u^4/24 + u^6/720 - u^8/40320 + u^10/3628800 - u^12/479001600 + u^14/87178291200 - u^16/20922789888000 + u^18/6402373705728000) (2 * y / 2 - 4 * y^3 / 24 + 6 * y^5 / 720 - 8 * y^7 / 40320 + 10 * y^9 / 3628800 - 12 * y^11 / 479001600 + 14 * y^13 / 87178291200 - 16 * y^15 / 20922789888000 + 18 * y^17 / 6402373705728000) y := ((((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7).add h8
    convert hd using 1 <;> ring
  have h := cos_ge_of_sin_le hx (fun t ht => sin_le_4 t ht)
    (by fun_prop : Continuous (fun t : ℝ => t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800 + t^13/6227020800 - t^15/1307674368000 + t^17/355687428096000)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h

/-- chain claim `sin_ge_4` -/
lemma sin_ge_4 (x : ℝ) (hx : 0 ≤ x) : x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 + x^13/6227020800 - x^15/1307674368000 + x^17/355687428096000 - x^19/121645100408832000 ≤ Real.sin x := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x, HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000 + u^17/355687428096000 - u^19/121645100408832000) (1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320 - y^10/3628800 + y^12/479001600 - y^14/87178291200 + y^16/20922789888000 - y^18/6402373705728000) y := by
    intro y hy
    have h0 : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun u : ℝ => u^3/6) (3 * y^2 / 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const 6
    have h2 : HasDerivAt (fun u : ℝ => u^5/120) (5 * y^4 / 120) y := by
      simpa using (hasDerivAt_pow 5 y).div_const 120
    have h3 : HasDerivAt (fun u : ℝ => u^7/5040) (7 * y^6 / 5040) y := by
      simpa using (hasDerivAt_pow 7 y).div_const 5040
    have h4 : HasDerivAt (fun u : ℝ => u^9/362880) (9 * y^8 / 362880) y := by
      simpa using (hasDerivAt_pow 9 y).div_const 362880
    have h5 : HasDerivAt (fun u : ℝ => u^11/39916800) (11 * y^10 / 39916800) y := by
      simpa using (hasDerivAt_pow 11 y).div_const 39916800
    have h6 : HasDerivAt (fun u : ℝ => u^13/6227020800) (13 * y^12 / 6227020800) y := by
      simpa using (hasDerivAt_pow 13 y).div_const 6227020800
    have h7 : HasDerivAt (fun u : ℝ => u^15/1307674368000) (15 * y^14 / 1307674368000) y := by
      simpa using (hasDerivAt_pow 15 y).div_const 1307674368000
    have h8 : HasDerivAt (fun u : ℝ => u^17/355687428096000) (17 * y^16 / 355687428096000) y := by
      simpa using (hasDerivAt_pow 17 y).div_const 355687428096000
    have h9 : HasDerivAt (fun u : ℝ => u^19/121645100408832000) (19 * y^18 / 121645100408832000) y := by
      simpa using (hasDerivAt_pow 19 y).div_const 121645100408832000
    have hd : HasDerivAt (fun u : ℝ => u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800 + u^13/6227020800 - u^15/1307674368000 + u^17/355687428096000 - u^19/121645100408832000) (1 - 3 * y^2 / 6 + 5 * y^4 / 120 - 7 * y^6 / 5040 + 9 * y^8 / 362880 - 11 * y^10 / 39916800 + 13 * y^12 / 6227020800 - 15 * y^14 / 1307674368000 + 17 * y^16 / 355687428096000 - 19 * y^18 / 121645100408832000) y := (((((((((h0).sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7).add h8).sub h9
    convert hd using 1 <;> ring
  have h := sin_ge_of_cos_ge hx (fun t ht => cos_ge_4 t ht)
    (by fun_prop : Continuous (fun t : ℝ => 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800 + t^12/479001600 - t^14/87178291200 + t^16/20922789888000 - t^18/6402373705728000)) hderiv
  try dsimp at h
  ring_nf at h ⊢
  exact h


/-! ## Part C. Numeric bounds for `sin`/`cos` at the grid points -/

lemma cos_half_le : Real.cos (1/2:ℝ) ≤ (8777:ℝ)/10000 := by
  have h := cos_le_4 (1/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_half_ge : (8775:ℝ)/10000 ≤ Real.cos (1/2:ℝ) := by
  have h := cos_ge_4 (1/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_one_le : Real.cos (1:ℝ) ≤ (54031:ℝ)/100000 := by
  have h := cos_le_4 (1:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_one_ge : (54029:ℝ)/100000 ≤ Real.cos (1:ℝ) := by
  have h := cos_ge_4 (1:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_three_half_le : Real.cos (3/2:ℝ) ≤ (7075:ℝ)/100000 := by
  have h := cos_le_4 (3/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_three_half_ge : (7073:ℝ)/100000 ≤ Real.cos (3/2:ℝ) := by
  have h := cos_ge_4 (3/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_two_le : Real.cos (2:ℝ) ≤ -(4161:ℝ)/10000 := by
  have h := cos_le_4 (2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_two_ge : -(4162:ℝ)/10000 ≤ Real.cos (2:ℝ) := by
  have h := cos_ge_4 (2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_five_half_le : Real.cos (5/2:ℝ) ≤ -(80114:ℝ)/100000 := by
  have h := cos_le_4 (5/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_five_half_ge : -(80115:ℝ)/100000 ≤ Real.cos (5/2:ℝ) := by
  have h := cos_ge_4 (5/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_three_le : Real.cos (3:ℝ) ≤ -(98999:ℝ)/100000 := by
  have h := cos_le_4 (3:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma cos_three_ge : -(99000:ℝ)/100000 ≤ Real.cos (3:ℝ) := by
  have h := cos_ge_4 (3:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_half_le : Real.sin (1/2:ℝ) ≤ (4795:ℝ)/10000 := by
  have h := sin_le_4 (1/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_half_ge : (4794:ℝ)/10000 ≤ Real.sin (1/2:ℝ) := by
  have h := sin_ge_4 (1/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_one_le : Real.sin (1:ℝ) ≤ (84148:ℝ)/100000 := by
  have h := sin_le_4 (1:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_one_ge : (84146:ℝ)/100000 ≤ Real.sin (1:ℝ) := by
  have h := sin_ge_4 (1:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_three_half_le : Real.sin (3/2:ℝ) ≤ (997496:ℝ)/1000000 := by
  have h := sin_le_4 (3/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_three_half_ge : (997494:ℝ)/1000000 ≤ Real.sin (3/2:ℝ) := by
  have h := sin_ge_4 (3/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_two_le : Real.sin (2:ℝ) ≤ (90931:ℝ)/100000 := by
  have h := sin_le_4 (2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_two_ge : (90929:ℝ)/100000 ≤ Real.sin (2:ℝ) := by
  have h := sin_ge_4 (2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_five_half_le : Real.sin (5/2:ℝ) ≤ (59849:ℝ)/100000 := by
  have h := sin_le_4 (5/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_five_half_ge : (59846:ℝ)/100000 ≤ Real.sin (5/2:ℝ) := by
  have h := sin_ge_4 (5/2:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_three_le : Real.sin (3:ℝ) ≤ (14113:ℝ)/100000 := by
  have h := sin_le_4 (3:ℝ) (by norm_num)
  norm_num at h
  nlinarith
lemma sin_three_ge : (14111:ℝ)/100000 ≤ Real.sin (3:ℝ) := by
  have h := sin_ge_4 (3:ℝ) (by norm_num)
  norm_num at h
  nlinarith


/-! ## Part C. Generic bounds for the sinc integral pieces -/

/-- `3/b - 3x/b² + x²/b³ ≤ 1/x` on `(0,b]` (difference is `(b-x)³/(b³x)`). -/
lemma inv_ge_quad (x b : ℝ) (hb : 0 < b) (hx : 0 < x) (hxb : x ≤ b) :
    (3 / b - 3 * x / b^2 + x^2 / b^3) ≤ (1 / x : ℝ) := by
  rw [← sub_nonneg]
  have h : (1 / x : ℝ) - (3 / b - 3 * x / b^2 + x^2 / b^3) = (b - x)^3 / (b^3 * x) := by
    field_simp [hb.ne', hx.ne']
    ring
  rw [h]
  positivity

/-- the secant chord of `y ↦ 1/(c+y)` on `[a,b]` -/
noncomputable def Chord (c a b : ℝ) : ℝ → ℝ :=
  fun y => 1 / (c + a) + ((1 / (c + b) - 1 / (c + a)) / (b - a)) * (y - a)

/-- chord above `1/(c+·)` on `[a,b]` (convexity, by pure algebra). -/
lemma chord_above {c a b y : ℝ} (hya : a ≤ y) (hyb : y ≤ b) (hab : a < b)
    (hca : 0 < c + a) :
    (1 / (c + y) : ℝ) ≤ Chord c a b y := by
  let L : ℝ := Chord c a b y
  have hcy : 0 < c + y := by linarith
  have hcb : 0 < c + b := by linarith
  have hba : 0 < b - a := by linarith
  have hdiff : L - 1 / (c + y) = (y - a) * (b - y) / ((c + a) * (c + b) * (c + y)) := by
    dsimp [L, Chord]
    field_simp [hca.ne', hcb.ne', hcy.ne', hba.ne']
    ring
  have hpos : 0 ≤ (y - a) * (b - y) / ((c + a) * (c + b) * (c + y)) := by
    positivity
  rw [← hdiff] at hpos
  linarith

/-- antiderivative of `sin`: `d(-cos) = sin`. -/
lemma hd_neg_cos (u : ℝ) : HasDerivAt (fun t : ℝ => -Real.cos t) (Real.sin u) u := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => -Real.cos t) u := by fun_prop
  have hv : deriv (fun t : ℝ => -Real.cos t) u = Real.sin u := by
    simp [Real.deriv_cos]
  exact hd.hasDerivAt.congr_deriv hv

/-- antiderivative of `x ↦ x·sin x`. -/
lemma hd_G2 (u : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t) (u * Real.sin u) u := by
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hu : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
  have hm : HasDerivAt (fun t : ℝ => t * Real.cos t) (Real.cos u - u * Real.sin u) u := by
    have hh := hu.mul hc
    refine hh.congr_deriv ?_
    ring
  have hsum := hs.sub hm
  refine hsum.congr_deriv ?_
  ring

/-- antiderivative of `x ↦ x²·sin x`. -/
lemma hd_G3 (u : ℝ) : HasDerivAt (fun t : ℝ => (2 - t^2) * Real.cos t + 2 * t * Real.sin t)
    (u^2 * Real.sin u) u := by
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have hp : HasDerivAt (fun t : ℝ => t^2) (2*u) u := by
    simpa using hasDerivAt_pow 2 u
  have hsub : HasDerivAt (fun t : ℝ => 2 - t^2) (-(2*u)) u := by
    have hc0 : HasDerivAt (fun _ : ℝ => (2:ℝ)) (0:ℝ) u := hasDerivAt_const u (2:ℝ)
    have hh := hc0.sub hp
    refine hh.congr_deriv ?_
    ring
  have hm1 : HasDerivAt (fun t : ℝ => (2 - t^2) * Real.cos t) (-(2*u)*Real.cos u + (2-u^2)*(-Real.sin u)) u := hsub.mul hc
  have htwo : HasDerivAt (fun t : ℝ => 2 * t) 2 u := by
    have hc0 : HasDerivAt (fun _ : ℝ => (2:ℝ)) (0:ℝ) u := hasDerivAt_const u (2:ℝ)
    have hh := hc0.mul (hasDerivAt_id u)
    refine hh.congr_deriv ?_
    ring
  have hm2 : HasDerivAt (fun t : ℝ => (2 * t) * Real.sin t) (2*Real.sin u + (2*u)*Real.cos u) u := htwo.mul hs
  have hsum := hm1.add hm2
  refine hsum.congr_deriv ?_
  ring

/-- combined antiderivative of `sin·q_b` where `q_b(u) = 3/b - 3u/b² + u²/b³`. -/
lemma hd_F {b u : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun t : ℝ => (3/b) * (-Real.cos t) - (3/b^2) * (Real.sin t - t * Real.cos t)
        + (1/b^3) * ((2 - t^2) * Real.cos t + 2 * t * Real.sin t))
      (Real.sin u * (3/b - 3*u/b^2 + u^2/b^3)) u := by
  have h1 : HasDerivAt (fun t : ℝ => (3/b) * (-Real.cos t)) ((3/b) * Real.sin u) u :=
    (hd_neg_cos u).const_mul (3/b)
  have h2 : HasDerivAt (fun t : ℝ => (3/b^2) * (Real.sin t - t * Real.cos t)) ((3/b^2) * (u * Real.sin u)) u :=
    (hd_G2 u).const_mul (3/b^2)
  have h3 : HasDerivAt (fun t : ℝ => (1/b^3) * ((2 - t^2) * Real.cos t + 2 * t * Real.sin t))
      ((1/b^3) * (u^2 * Real.sin u)) u := (hd_G3 u).const_mul (1/b^3)
  have h := h1.sub h2
  have hsum := h.add h3
  refine hsum.congr_deriv ?_
  ring

/-- `∫_a^b sin(x)·q_b(x) dx` closed form. -/
lemma int_sin_q (a b : ℝ) (hb : b ≠ 0) :
    (∫ x in a..b, Real.sin x * (3/b - 3*x/b^2 + x^2/b^3)) =
      (3/b) * (Real.cos a - Real.cos b) - (3/b^2) * ((Real.sin b - b * Real.cos b) - (Real.sin a - a * Real.cos a))
        + (1/b^3) * (((2 - b^2) * Real.cos b + 2*b*Real.sin b) - ((2 - a^2)*Real.cos a + 2*a*Real.sin a)) := by
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt
      (fun t : ℝ => (3/b) * (-Real.cos t) - (3/b^2) * (Real.sin t - t * Real.cos t)
        + (1/b^3) * ((2 - t^2) * Real.cos t + 2 * t * Real.sin t))
      (Real.sin y * (3/b - 3*y/b^2 + y^2/b^3)) y := by
    intro y hy
    exact hd_F hb
  have hcont : Continuous (fun x : ℝ => Real.sin x * (3/b - 3*x/b^2 + x^2/b^3)) := by fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin x * (3/b - 3*x/b^2 + x^2/b^3)) volume a b := by
    exact hcont.intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hF]
  ring

/-- pointwise: `sin x·q_b(x) ≤ sinc x` for `0 < x ≤ b ≤ π`. -/
lemma sinc_ge_sin_mul_q {a b : ℝ} (hb : 0 < b) (hpi : b ≤ Real.pi)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hx0 : 0 < x) :
    Real.sin x * (3/b - 3*x/b^2 + x^2/b^3) ≤ Real.sinc x := by
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (le_trans hx.2 hpi)
  have hq : (3 / b - 3 * x / b^2 + x^2 / b^3) ≤ (1 / x : ℝ) := inv_ge_quad x b hb hx0 hx.2
  have hmul : Real.sin x * (3 / b - 3 * x / b^2 + x^2 / b^3) ≤ Real.sin x * (1 / x) :=
    mul_le_mul_of_nonneg_left hq hsin
  rw [Real.sinc_of_ne_zero (ne_of_gt hx0)]
  simpa [div_eq_mul_inv] using hmul

/-- `∫_a^b sin·q ≤ ∫_a^b sinc` for `0 < a ≤ b ≤ π`. -/
lemma int_sinc_ge_int_sin_q {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hpi : b ≤ Real.pi) :
    (∫ x in a..b, Real.sin x * (3/b - 3*x/b^2 + x^2/b^3)) ≤ ∫ x in a..b, Real.sinc x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hqcont : Continuous (fun x : ℝ => Real.sin x * (3/b - 3*x/b^2 + x^2/b^3)) := by fun_prop
  refine intervalIntegral.integral_mono_on hab (hqcont.intervalIntegrable _ _)
    (Real.continuous_sinc.intervalIntegrable _ _) ?_
  intro x hx
  exact sinc_ge_sin_mul_q hb hpi x hx (lt_of_lt_of_le ha hx.1)

/-- `sinc ≥ 0` on `[a,b] ⊆ [0,π]`. -/
lemma sinc_nonneg_of_mem (a b : ℝ) (ha : 0 ≤ a) (hpi : b ≤ Real.pi)
    (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ Real.sinc x := by
  by_cases hx0 : x = 0
  · subst x; simp
  · have hxpos : 0 < x := lt_of_le_of_ne (le_trans ha hx.1) (Ne.symm hx0)
    rw [Real.sinc_of_ne_zero hx0]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hxpos.le (le_trans hx.2 hpi))
      (le_of_lt hxpos)

/-- `∫_a^b sinc ≥ 0` on `[a,b] ⊆ [0,π]` with `a ≤ b`. -/
lemma int_sinc_nonneg (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hpi : b ≤ Real.pi) :
    (0 : ℝ) ≤ ∫ x in a..b, Real.sinc x := by
  refine intervalIntegral.integral_nonneg hab ?_
  intro x hx
  exact sinc_nonneg_of_mem a b ha hpi x hx


/-! ## Part C (cont). Numeric lower bounds for the positive pieces -/

lemma piece_1_2 : (438184:ℝ)/1000000 ≤ ∫ x in (1/2:ℝ)..(1:ℝ), Real.sinc x := by
  have hcomp := int_sinc_ge_int_sin_q (a := (1/2:ℝ)) (b := (1:ℝ)) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have hftc := int_sin_q (1/2:ℝ) (1:ℝ) (by norm_num)
  have hlow : (438184:ℝ)/1000000 ≤ (3/(1:ℝ)) * (Real.cos (1/2:ℝ) - Real.cos (1:ℝ)) - (3/(1:ℝ)^2) * ((Real.sin (1:ℝ) - (1:ℝ) * Real.cos (1:ℝ)) - (Real.sin (1/2:ℝ) - (1/2:ℝ) * Real.cos (1/2:ℝ))) + (1/(1:ℝ)^3) * (((2 - (1:ℝ)^2) * Real.cos (1:ℝ) + 2*(1:ℝ)*Real.sin (1:ℝ)) - ((2 - (1/2:ℝ)^2) * Real.cos (1/2:ℝ) + 2*(1/2:ℝ)*Real.sin (1/2:ℝ))) := by
    nlinarith [cos_half_le, cos_half_ge, cos_one_le, cos_one_ge, sin_half_le, sin_half_ge, sin_one_le, sin_one_ge]
  rw [hftc] at hcomp
  linarith

lemma piece_2_3 : (374838:ℝ)/1000000 ≤ ∫ x in (1:ℝ)..(3/2:ℝ), Real.sinc x := by
  have hcomp := int_sinc_ge_int_sin_q (a := (1:ℝ)) (b := (3/2:ℝ)) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have hftc := int_sin_q (1:ℝ) (3/2:ℝ) (by norm_num)
  have hlow : (374838:ℝ)/1000000 ≤ (3/(3/2:ℝ)) * (Real.cos (1:ℝ) - Real.cos (3/2:ℝ)) - (3/(3/2:ℝ)^2) * ((Real.sin (3/2:ℝ) - (3/2:ℝ) * Real.cos (3/2:ℝ)) - (Real.sin (1:ℝ) - (1:ℝ) * Real.cos (1:ℝ))) + (1/(3/2:ℝ)^3) * (((2 - (3/2:ℝ)^2) * Real.cos (3/2:ℝ) + 2*(3/2:ℝ)*Real.sin (3/2:ℝ)) - ((2 - (1:ℝ)^2) * Real.cos (1:ℝ) + 2*(1:ℝ)*Real.sin (1:ℝ))) := by
    nlinarith [cos_one_le, cos_one_ge, cos_three_half_le, cos_three_half_ge, sin_one_le, sin_one_ge, sin_three_half_le, sin_three_half_ge]
  rw [hftc] at hcomp
  linarith

lemma piece_3_4 : (279491:ℝ)/1000000 ≤ ∫ x in (3/2:ℝ)..(2:ℝ), Real.sinc x := by
  have hcomp := int_sinc_ge_int_sin_q (a := (3/2:ℝ)) (b := (2:ℝ)) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have hftc := int_sin_q (3/2:ℝ) (2:ℝ) (by norm_num)
  have hlow : (279491:ℝ)/1000000 ≤ (3/(2:ℝ)) * (Real.cos (3/2:ℝ) - Real.cos (2:ℝ)) - (3/(2:ℝ)^2) * ((Real.sin (2:ℝ) - (2:ℝ) * Real.cos (2:ℝ)) - (Real.sin (3/2:ℝ) - (3/2:ℝ) * Real.cos (3/2:ℝ))) + (1/(2:ℝ)^3) * (((2 - (2:ℝ)^2) * Real.cos (2:ℝ) + 2*(2:ℝ)*Real.sin (2:ℝ)) - ((2 - (3/2:ℝ)^2) * Real.cos (3/2:ℝ) + 2*(3/2:ℝ)*Real.sin (3/2:ℝ))) := by
    nlinarith [cos_three_half_le, cos_three_half_ge, cos_two_le, cos_two_ge, sin_three_half_le, sin_three_half_ge, sin_two_le, sin_two_ge]
  rw [hftc] at hcomp
  linarith

lemma piece_4_5 : (172670:ℝ)/1000000 ≤ ∫ x in (2:ℝ)..(5/2:ℝ), Real.sinc x := by
  have hcomp := int_sinc_ge_int_sin_q (a := (2:ℝ)) (b := (5/2:ℝ)) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have hftc := int_sin_q (2:ℝ) (5/2:ℝ) (by norm_num)
  have hlow : (172670:ℝ)/1000000 ≤ (3/(5/2:ℝ)) * (Real.cos (2:ℝ) - Real.cos (5/2:ℝ)) - (3/(5/2:ℝ)^2) * ((Real.sin (5/2:ℝ) - (5/2:ℝ) * Real.cos (5/2:ℝ)) - (Real.sin (2:ℝ) - (2:ℝ) * Real.cos (2:ℝ))) + (1/(5/2:ℝ)^3) * (((2 - (5/2:ℝ)^2) * Real.cos (5/2:ℝ) + 2*(5/2:ℝ)*Real.sin (5/2:ℝ)) - ((2 - (2:ℝ)^2) * Real.cos (2:ℝ) + 2*(2:ℝ)*Real.sin (2:ℝ))) := by
    nlinarith [cos_two_le, cos_two_ge, cos_five_half_le, cos_five_half_ge, sin_two_le, sin_two_ge, sin_five_half_le, sin_five_half_ge]
  rw [hftc] at hcomp
  linarith

lemma piece_5_6 : (70011:ℝ)/1000000 ≤ ∫ x in (5/2:ℝ)..(3:ℝ), Real.sinc x := by
  have hcomp := int_sinc_ge_int_sin_q (a := (5/2:ℝ)) (b := (3:ℝ)) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have hftc := int_sin_q (5/2:ℝ) (3:ℝ) (by norm_num)
  have hlow : (70011:ℝ)/1000000 ≤ (3/(3:ℝ)) * (Real.cos (5/2:ℝ) - Real.cos (3:ℝ)) - (3/(3:ℝ)^2) * ((Real.sin (3:ℝ) - (3:ℝ) * Real.cos (3:ℝ)) - (Real.sin (5/2:ℝ) - (5/2:ℝ) * Real.cos (5/2:ℝ))) + (1/(3:ℝ)^3) * (((2 - (3:ℝ)^2) * Real.cos (3:ℝ) + 2*(3:ℝ)*Real.sin (3:ℝ)) - ((2 - (5/2:ℝ)^2) * Real.cos (5/2:ℝ) + 2*(5/2:ℝ)*Real.sin (5/2:ℝ))) := by
    nlinarith [cos_five_half_le, cos_five_half_ge, cos_three_le, cos_three_ge, sin_five_half_le, sin_five_half_ge, sin_three_le, sin_three_ge]
  rw [hftc] at hcomp
  linarith






/-! ## Part C (negative part). Bound for `∫_π^{2π} sinc` -/

/-- `sin/(c+y) ≤ sin·Chord` pointwise on `[a,b] ⊆ [0,π]`. -/
lemma sin_div_le_sin_chord {c a b y : ℝ} (hya : a ≤ y) (hyb : y ≤ b) (hab : a < b)
    (hca : 0 < c + a) (ha0 : 0 ≤ a) (hpi : b ≤ Real.pi) :
    Real.sin y / (c + y) ≤ Real.sin y * Chord c a b y := by
  have hsin : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi (le_trans ha0 hya) (le_trans hyb hpi)
  have hc := chord_above (c := c) hya hyb hab hca
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hc hsin

/-- `∫_a^b sin/(c+·) ≤ ∫_a^b sin·Chord`. -/
lemma int_sin_div_le_chord {c a b : ℝ} (hab : a < b) (hca : 0 < c + a) (ha0 : 0 ≤ a)
    (hpi : b ≤ Real.pi) :
    (∫ y in a..b, Real.sin y / (c + y)) ≤ ∫ y in a..b, Real.sin y * Chord c a b y := by
  have hfcont : ContinuousOn (fun y : ℝ => Real.sin y / (c + y)) (Set.uIcc a b) := by
    apply ContinuousOn.div
    · exact Continuous.continuousOn Real.continuous_sin
    · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => c + y))
    · intro y hy
      rw [Set.uIcc_of_le hab.le] at hy
      have hya : a ≤ y := hy.1
      have hcy : 0 < c + y := by linarith
      exact ne_of_gt hcy
  have hgcont : Continuous (fun y : ℝ => Real.sin y * Chord c a b y) := by
    unfold Chord
    fun_prop
  refine intervalIntegral.integral_mono_on hab.le (ContinuousOn.intervalIntegrable hfcont)
    (hgcont.intervalIntegrable _ _) ?_
  intro y hy
  exact sin_div_le_sin_chord (a := a) hy.1 hy.2 hab hca ha0 hpi

/-- antiderivative of `sin·Chord` -/
lemma hd_H (c a b u : ℝ) :
    HasDerivAt (fun t : ℝ => (-(1/(c+a))) * Real.cos t
        + ((1/(c+b) - 1/(c+a)) / (b-a)) * ((Real.sin t - t * Real.cos t) + a * Real.cos t))
      (Real.sin u * Chord c a b u) u := by
  let A : ℝ := 1 / (c + a)
  let s : ℝ := (1 / (c + b) - 1 / (c + a)) / (b - a)
  have h1 : HasDerivAt (fun t : ℝ => (-A) * Real.cos t) ((-A) * (-Real.sin u)) u :=
    (Real.hasDerivAt_cos u).const_mul (-A)
  have h2 : HasDerivAt (fun t : ℝ => (Real.sin t - t * Real.cos t) + a * Real.cos t)
      (u * Real.sin u + a * (-Real.sin u)) u := by
    have hh := (hd_G2 u).add ((Real.hasDerivAt_cos u).const_mul a)
    refine hh.congr_deriv ?_
    ring
  have h3 := (h2.const_mul s)
  have hsum := h1.add h3
  refine hsum.congr_deriv ?_
  dsimp [A, s, Chord]
  ring

/-- FTC: `∫_a^b sin·Chord` closed form. -/
lemma int_sin_chord (c a b : ℝ) :
    (∫ y in a..b, Real.sin y * Chord c a b y) =
      (1 / (c + a)) * (Real.cos a - Real.cos b)
        + ((1 / (c + b) - 1 / (c + a)) / (b - a)) *
          (((Real.sin b - b * Real.cos b) - (Real.sin a - a * Real.cos a)) - a * (Real.cos a - Real.cos b)) := by
  let A : ℝ := 1 / (c + a)
  let s : ℝ := (1 / (c + b) - 1 / (c + a)) / (b - a)
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt
      (fun t : ℝ => (-A) * Real.cos t + s * ((Real.sin t - t * Real.cos t) + a * Real.cos t))
      (Real.sin y * Chord c a b y) y := by
    intro y hy
    simpa [A, s] using hd_H c a b y
  have hcont : Continuous (fun y : ℝ => Real.sin y * Chord c a b y) := by
    unfold Chord
    fun_prop
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  have hmain : (∫ y in a..b, Real.sin y * Chord c a b y) =
      (-A) * Real.cos b + s * ((Real.sin b - b * Real.cos b) + a * Real.cos b)
        - ((-A) * Real.cos a + s * ((Real.sin a - a * Real.cos a) + a * Real.cos a)) := by
    simpa using hF
  rw [hmain]
  dsimp [A, s]
  ring

lemma chord_piece_0 : (∫ y in (0:ℝ)..(1/2:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (35441:ℝ)/1000000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (0:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (0:ℝ)) (b := (1/2:ℝ))
  have h3 : ((2000:ℝ)/6283) * (Real.cos (0:ℝ) - Real.cos (1/2:ℝ)) + ((-4000000:ℝ)/45759089) * (((Real.sin (1/2:ℝ) - (1/2:ℝ) * Real.cos (1/2:ℝ)) - (Real.sin (0:ℝ) - (0:ℝ) * Real.cos (0:ℝ))) - (0:ℝ) * (Real.cos (0:ℝ) - Real.cos (1/2:ℝ))) ≤ (35441:ℝ)/1000000 := by
    nlinarith [(by norm_num : Real.cos (0:ℝ) ≤ (1:ℝ)), (by norm_num : (1:ℝ) ≤ Real.cos (0:ℝ)), (by norm_num : Real.sin (0:ℝ) ≤ (0:ℝ)), (by norm_num : (0:ℝ) ≤ Real.sin (0:ℝ)), cos_half_le, cos_half_ge, sin_half_le, sin_half_ge]
  rw [h2] at h1
  nlinarith [h1, h3]

lemma chord_piece_1 : (∫ y in (1/2:ℝ)..(1:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (86569:ℝ)/1000000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (1/2:ℝ)) (b := (1:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (1/2:ℝ)) (b := (1:ℝ))
  have h3 : ((2000:ℝ)/7283) * (Real.cos (1/2:ℝ) - Real.cos (1:ℝ)) + ((-4000000:ℝ)/60325089) * (((Real.sin (1:ℝ) - (1:ℝ) * Real.cos (1:ℝ)) - (Real.sin (1/2:ℝ) - (1/2:ℝ) * Real.cos (1/2:ℝ))) - (1/2:ℝ) * (Real.cos (1/2:ℝ) - Real.cos (1:ℝ))) ≤ (86569:ℝ)/1000000 := by
    nlinarith [cos_half_le, cos_half_ge, sin_half_le, sin_half_ge, cos_one_le, cos_one_ge, sin_one_le, sin_one_ge]
  rw [h2] at h1
  nlinarith [h1, h3]

lemma chord_piece_2 : (∫ y in (1:ℝ)..(3/2:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (26777:ℝ)/250000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (1:ℝ)) (b := (3/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (1:ℝ)) (b := (3/2:ℝ))
  have h3 : ((2000:ℝ)/8283) * (Real.cos (1:ℝ) - Real.cos (3/2:ℝ)) + ((-4000000:ℝ)/76891089) * (((Real.sin (3/2:ℝ) - (3/2:ℝ) * Real.cos (3/2:ℝ)) - (Real.sin (1:ℝ) - (1:ℝ) * Real.cos (1:ℝ))) - (1:ℝ) * (Real.cos (1:ℝ) - Real.cos (3/2:ℝ))) ≤ (26777:ℝ)/250000 := by
    nlinarith [cos_one_le, cos_one_ge, sin_one_le, sin_one_ge, cos_three_half_le, cos_three_half_ge, sin_three_half_le, sin_three_half_ge]
  rw [h2] at h1
  nlinarith [h1, h3]

lemma chord_piece_3 : (∫ y in (3/2:ℝ)..(2:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (99889:ℝ)/1000000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (3/2:ℝ)) (b := (2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (3/2:ℝ)) (b := (2:ℝ))
  have h3 : ((2000:ℝ)/9283) * (Real.cos (3/2:ℝ) - Real.cos (2:ℝ)) + ((-4000000:ℝ)/95457089) * (((Real.sin (2:ℝ) - (2:ℝ) * Real.cos (2:ℝ)) - (Real.sin (3/2:ℝ) - (3/2:ℝ) * Real.cos (3/2:ℝ))) - (3/2:ℝ) * (Real.cos (3/2:ℝ) - Real.cos (2:ℝ))) ≤ (99889:ℝ)/1000000 := by
    nlinarith [cos_three_half_le, cos_three_half_ge, sin_three_half_le, sin_three_half_ge, cos_two_le, cos_two_ge, sin_two_le, sin_two_ge]
  rw [h2] at h1
  nlinarith [h1, h3]

lemma chord_piece_4 : (∫ y in (2:ℝ)..(5/2:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (35899:ℝ)/500000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (2:ℝ)) (b := (5/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (2:ℝ)) (b := (5/2:ℝ))
  have h3 : ((2000:ℝ)/10283) * (Real.cos (2:ℝ) - Real.cos (5/2:ℝ)) + ((-4000000:ℝ)/116023089) * (((Real.sin (5/2:ℝ) - (5/2:ℝ) * Real.cos (5/2:ℝ)) - (Real.sin (2:ℝ) - (2:ℝ) * Real.cos (2:ℝ))) - (2:ℝ) * (Real.cos (2:ℝ) - Real.cos (5/2:ℝ))) ≤ (35899:ℝ)/500000 := by
    nlinarith [cos_two_le, cos_two_ge, sin_two_le, sin_two_ge, cos_five_half_le, cos_five_half_ge, sin_five_half_le, sin_five_half_ge]
  rw [h2] at h1
  nlinarith [h1, h3]

lemma chord_piece_5 : (∫ y in (5/2:ℝ)..(3:ℝ), Real.sin y / ((6283:ℝ)/2000 + y)) ≤ (4049:ℝ)/125000 := by
  have h1 := int_sin_div_le_chord (c := (6283:ℝ)/2000) (a := (5/2:ℝ)) (b := (3:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
  have h2 := int_sin_chord (c := (6283:ℝ)/2000) (a := (5/2:ℝ)) (b := (3:ℝ))
  have h3 : ((2000:ℝ)/11283) * (Real.cos (5/2:ℝ) - Real.cos (3:ℝ)) + ((-4000000:ℝ)/138589089) * (((Real.sin (3:ℝ) - (3:ℝ) * Real.cos (3:ℝ)) - (Real.sin (5/2:ℝ) - (5/2:ℝ) * Real.cos (5/2:ℝ))) - (5/2:ℝ) * (Real.cos (5/2:ℝ) - Real.cos (3:ℝ))) ≤ (4049:ℝ)/125000 := by
    nlinarith [cos_five_half_le, cos_five_half_ge, sin_five_half_le, sin_five_half_ge, cos_three_le, cos_three_ge, sin_three_le, sin_three_ge]
  rw [h2] at h1
  nlinarith [h1, h3]



/-! ## Part C (assembly). The three integral bounds -/

/-- `1 - x²/6 + x⁴/120 - x⁶/5040 ≤ sinc x` on `[0, 1/2]`. -/
lemma sinc_ge_S4 (x : ℝ) (hx0 : 0 ≤ x) (hx12 : x ≤ 1/2) :
    1 - x^2/6 + x^4/120 - x^6/5040 ≤ Real.sinc x := by
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · simp
  · have hsin : x - x^3/6 + x^5/120 - x^7/5040 ≤ Real.sin x := sin_ge_1 x hx0
    rw [Real.sinc_of_ne_zero (ne_of_gt hxpos)]
    rw [le_div_iff₀ hxpos]
    nlinarith [hsin]

/-- antiderivative of `1 - x²/6 + x⁴/120 - x⁶/5040`. -/
lemma hd_S4 (u : ℝ) : HasDerivAt (fun t : ℝ => t - t^3/18 + t^5/600 - t^7/35280)
    (1 - u^2/6 + u^4/120 - u^6/5040) u := by
  have h0 : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
  have h1 : HasDerivAt (fun t : ℝ => t^3/18) (3*u^2/18) u := by
    simpa using (hasDerivAt_pow 3 u).div_const 18
  have h2 : HasDerivAt (fun t : ℝ => t^5/600) (5*u^4/600) u := by
    simpa using (hasDerivAt_pow 5 u).div_const 600
  have h3 : HasDerivAt (fun t : ℝ => t^7/35280) (7*u^6/35280) u := by
    simpa using (hasDerivAt_pow 7 u).div_const 35280
  exact (((h0.sub h1).add h2).sub h3).congr_deriv (by ring)

/-- `∫_0^{1/2} sinc ≥ 0.4930`. -/
lemma int_0_half_sinc_ge : (4930:ℝ)/10000 ≤ ∫ x in (0:ℝ)..(1/2:ℝ), Real.sinc x := by
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) (1/2:ℝ), 1 - x^2/6 + x^4/120 - x^6/5040 ≤ Real.sinc x := by
    intro x hx
    exact sinc_ge_S4 x hx.1 hx.2
  have hcont : Continuous (fun x : ℝ => 1 - x^2/6 + x^4/120 - x^6/5040) := by fun_prop
  have hmono : (∫ x in (0:ℝ)..(1/2:ℝ), 1 - x^2/6 + x^4/120 - x^6/5040)
      ≤ ∫ x in (0:ℝ)..(1/2:ℝ), Real.sinc x := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      (Real.continuous_sinc.intervalIntegrable _ _) hpt
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) (1/2:ℝ),
      HasDerivAt (fun t : ℝ => t - t^3/18 + t^5/600 - t^7/35280)
        (1 - y^2/6 + y^4/120 - y^6/5040) y := by
    intro y hy
    exact hd_S4 y
  have hval := int_zero_eq_sub (by norm_num : (0:ℝ) ≤ 1/2) hcont hderiv
  rw [hval] at hmono
  norm_num at hmono
  linarith

/-- split integral: `∫ a..c = ∫ a..b + ∫ b..c`. -/
lemma int_add_adj {a b c : ℝ} (f : ℝ → ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hf : Continuous f) :
    (∫ x in a..b, f x) + (∫ x in b..c, f x) = ∫ x in a..c, f x := by
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)

/-- `∫_0^3 sinc ≥ 0.4930 + (the five piece lower bounds)`. -/
lemma int_0_3_sinc_ge :
    ((4930:ℝ)/10000 + (438184:ℝ)/1000000 + (374838:ℝ)/1000000 + (279491:ℝ)/1000000
      + (172670:ℝ)/1000000 + (70011:ℝ)/1000000)
      ≤ ∫ x in (0:ℝ)..(3:ℝ), Real.sinc x := by
  have h1 := int_add_adj (f := Real.sinc) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 3)
    Real.continuous_sinc
  have h2 := int_add_adj (f := Real.sinc) (by norm_num : (1/2:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 3)
    Real.continuous_sinc
  have h3 := int_add_adj (f := Real.sinc) (by norm_num : (1:ℝ) ≤ 3/2) (by norm_num : (3/2:ℝ) ≤ 3)
    Real.continuous_sinc
  have h4 := int_add_adj (f := Real.sinc) (by norm_num : (3/2:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 3)
    Real.continuous_sinc
  have h5 := int_add_adj (f := Real.sinc) (by norm_num : (2:ℝ) ≤ 5/2) (by norm_num : (5/2:ℝ) ≤ 3)
    Real.continuous_sinc
  rw [← h1, ← h2, ← h3, ← h4, ← h5]
  have hA := int_0_half_sinc_ge
  have hB := piece_1_2
  have hC := piece_2_3
  have hD := piece_3_4
  have hE := piece_4_5
  have hF := piece_5_6
  linarith

/-- `∫_3^π sin/(c+·) ≤ 1/40`. -/
lemma int_3_pi_div_tail : (∫ y in (3:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y))
    ≤ (1:ℝ)/40 := by
  have h1 : (∫ y in (3:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y))
      ≤ ∫ y in (3:ℝ)..Real.pi, (1:ℝ) / ((6283:ℝ)/2000 + 3) := by
    have hf : ContinuousOn (fun y : ℝ => Real.sin y / ((6283:ℝ)/2000 + y)) (Set.uIcc 3 Real.pi) := by
      apply ContinuousOn.div
      · exact Continuous.continuousOn Real.continuous_sin
      · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => (6283:ℝ)/2000 + y))
      · intro y hy
        rw [Set.uIcc_of_le (by linarith [Real.pi_gt_three] : (3:ℝ) ≤ Real.pi)] at hy
        have hy3 : (3:ℝ) ≤ y := hy.1
        have hc : (0:ℝ) < (6283:ℝ)/2000 + y := by nlinarith
        exact ne_of_gt hc
    have hg : Continuous (fun y : ℝ => (1:ℝ) / ((6283:ℝ)/2000 + 3)) := by fun_prop
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_gt_three] : (3:ℝ) ≤ Real.pi)
      (ContinuousOn.intervalIntegrable hf) (hg.intervalIntegrable _ _) ?_
    intro y hy
    have hy3 : (3:ℝ) ≤ y := hy.1
    have hsin : Real.sin y ≤ 1 := Real.sin_le_one y
    have hpos : (0:ℝ) < (6283:ℝ)/2000 + y := by nlinarith
    calc
      Real.sin y / ((6283:ℝ)/2000 + y) ≤ (1:ℝ) / ((6283:ℝ)/2000 + y) := by
        exact div_le_div_of_nonneg_right hsin hpos.le
      _ ≤ (1:ℝ) / ((6283:ℝ)/2000 + 3) := by
        rw [div_le_div_iff₀] <;> nlinarith
  have h2 : (∫ y in (3:ℝ)..Real.pi, (1:ℝ) / ((6283:ℝ)/2000 + 3)) =
      (Real.pi - 3) * ((1:ℝ) / ((6283:ℝ)/2000 + 3)) := by
    simp [intervalIntegral.integral_const]
  rw [h2] at h1
  have hpi : Real.pi - 3 ≤ (3:ℝ)/20 := by
    have h := Real.pi_lt_d2
    nlinarith
  have hden : (1:ℝ) / ((6283:ℝ)/2000 + 3) ≤ 1 / 6 := by
    rw [div_le_div_iff₀] <;> norm_num
  have hprod : (Real.pi - 3) * ((1:ℝ) / ((6283:ℝ)/2000 + 3)) ≤ (1:ℝ)/40 := by
    calc
      (Real.pi - 3) * ((1:ℝ) / ((6283:ℝ)/2000 + 3))
          ≤ (3:ℝ)/20 * (1/6) := mul_le_mul hpi hden (by positivity) (by linarith)
      _ = (1:ℝ)/40 := by norm_num
  exact le_trans h1 hprod


/-- `∫_a^b g` integrable for `0 ≤ a ≤ b`. -/
lemma g_interval_integrable {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) :
    IntervalIntegrable (fun y : ℝ => Real.sin y / ((6283:ℝ)/2000 + y)) volume a b := by
  have hf : ContinuousOn (fun y : ℝ => Real.sin y / ((6283:ℝ)/2000 + y)) (Set.uIcc a b) := by
    apply ContinuousOn.div
    · exact Continuous.continuousOn Real.continuous_sin
    · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => (6283:ℝ)/2000 + y))
    · intro y hy
      rw [Set.uIcc_of_le hab] at hy
      have hya : a ≤ y := hy.1
      have hc : (0:ℝ) < (6283:ℝ)/2000 + y := by nlinarith
      exact ne_of_gt hc
  exact ContinuousOn.intervalIntegrable hf

/-- split `∫ a..c = ∫ a..b + ∫ b..c` for the integrable kernel `sin/(c+·)`. -/
lemma g_add_adj (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (ha : 0 ≤ a) :
    (∫ y in a..b, Real.sin y / ((6283:ℝ)/2000 + y))
        + (∫ y in b..c, Real.sin y / ((6283:ℝ)/2000 + y))
      = ∫ y in a..c, Real.sin y / ((6283:ℝ)/2000 + y) :=
  intervalIntegral.integral_add_adjacent_intervals (g_interval_integrable hab ha)
    (g_interval_integrable hbc (le_trans ha hab))

/-- `∫_0^3 sin/(c+·) ≤ Σ` of the six chord-piece bounds. -/
lemma int_0_3_div_le :
    (∫ y in (0:ℝ)..(3:ℝ), Real.sin y / ((6283:ℝ)/2000 + y))
      ≤ ((35441:ℝ)/1000000 + (86569:ℝ)/1000000 + (107108:ℝ)/1000000
        + (99889:ℝ)/1000000 + (71798:ℝ)/1000000 + (32392:ℝ)/1000000) := by
  have h1 := g_add_adj (0:ℝ) (1/2:ℝ) (3:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have h2 := g_add_adj (1/2:ℝ) (1:ℝ) (3:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have h3 := g_add_adj (1:ℝ) (3/2:ℝ) (3:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have h4 := g_add_adj (3/2:ℝ) (2:ℝ) (3:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have h5 := g_add_adj (2:ℝ) (5/2:ℝ) (3:ℝ) (by norm_num) (by norm_num) (by norm_num)
  rw [← h1, ← h2, ← h3, ← h4, ← h5]
  have ha := chord_piece_0
  have hb := chord_piece_1
  have hc := chord_piece_2
  have hd := chord_piece_3
  have he := chord_piece_4
  have hf := chord_piece_5
  linarith

/-- `3.1415 ≤ π`. -/
lemma c_le_pi : (6283:ℝ)/2000 ≤ Real.pi := by
  exact le_of_lt (by nlinarith [Real.pi_gt_d4])

/-- shift-substitution: `∫_π^{2π} -sin x / x = ∫_0^π sin y / (y+π)`. -/
lemma subst_neg_sin : (∫ x in Real.pi..2*Real.pi, -(Real.sin x) / x) =
    ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := by
  have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := Real.pi)
    (f := fun x : ℝ => -Real.sin x / x) Real.pi
  calc
    (∫ x in Real.pi..2*Real.pi, -(Real.sin x) / x)
        = ∫ x in (0:ℝ)..Real.pi, (-Real.sin (x + Real.pi)) / (x + Real.pi) := by
            simpa [two_mul] using h.symm
    _ = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := by
            apply intervalIntegral.integral_congr
            intro y hy
            dsimp
            rw [Real.sin_add_pi]
            ring

/-- negative part: `-S ≤ ∫_π^{2π} sinc` with `S = 0.433197 + 0.025`. -/
lemma int_pi_2pi_ge_negS :
    -(((433197:ℝ)/1000000) + (1:ℝ)/40) ≤ ∫ x in Real.pi..2 * Real.pi, Real.sinc x := by
  have hA : (∫ x in Real.pi..2 * Real.pi, -(Real.sinc x))
      = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := by
    calc
      (∫ x in Real.pi..2 * Real.pi, -(Real.sinc x))
          = ∫ x in Real.pi..2 * Real.pi, -(Real.sin x) / x := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp
              have hx0 : x ≠ 0 := by
                have hx' : x ∈ Set.Icc Real.pi (2 * Real.pi) := by
                  have hxu := hx
                  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hxu
                  exact hxu
                have hxpos : (0:ℝ) < x := lt_of_lt_of_le Real.pi_pos hx'.1
                exact ne_of_gt hxpos
              rw [Real.sinc_of_ne_zero hx0]
              ring
      _ = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := subst_neg_sin
  have hM : (∫ y in (0:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y))
      ≤ ((35441:ℝ)/1000000 + (86569:ℝ)/1000000 + (107108:ℝ)/1000000
        + (99889:ℝ)/1000000 + (71798:ℝ)/1000000 + (32392:ℝ)/1000000) + (1:ℝ)/40 := by
    have hsplit : (∫ y in (0:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y))
        = (∫ y in (0:ℝ)..(3:ℝ), Real.sin y / ((6283:ℝ)/2000 + y))
          + (∫ y in (3:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y)) := by
      exact (g_add_adj (0:ℝ) (3:ℝ) Real.pi (by norm_num) (by linarith [Real.pi_gt_three]) (by norm_num)).symm
    rw [hsplit]
    have h03 := int_0_3_div_le
    have htail := int_3_pi_div_tail
    linarith
  have hcπ : (∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi))
      ≤ ∫ y in (0:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y) := by
    have hf : ContinuousOn (fun y : ℝ => Real.sin y / (y + Real.pi)) (Set.uIcc 0 Real.pi) := by
      apply ContinuousOn.div
      · exact Continuous.continuousOn Real.continuous_sin
      · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => y + Real.pi))
      · intro y hy
        have hy' : y ∈ Set.Icc (0:ℝ) Real.pi := by
          simpa [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi)] using hy
        have : (0:ℝ) < y + Real.pi := by nlinarith [Real.pi_pos, hy'.1]
        exact ne_of_gt this
    have hgcont : ContinuousOn (fun y : ℝ => Real.sin y / ((6283:ℝ)/2000 + y)) (Set.uIcc 0 Real.pi) := by
      apply ContinuousOn.div
      · exact Continuous.continuousOn Real.continuous_sin
      · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => (6283:ℝ)/2000 + y))
      · intro y hy
        have hy' : y ∈ Set.Icc (0:ℝ) Real.pi := by
          simpa [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi)] using hy
        have : (0:ℝ) < (6283:ℝ)/2000 + y := by nlinarith [hy'.1]
        exact ne_of_gt this
    refine intervalIntegral.integral_mono_on (by positivity) (ContinuousOn.intervalIntegrable hf)
      (ContinuousOn.intervalIntegrable hgcont) ?_
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hsin : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 hy.2
    have hle : (1 / (y + Real.pi) : ℝ) ≤ 1 / ((6283:ℝ)/2000 + y) := by
      rw [div_le_div_iff₀]
      · nlinarith [c_le_pi]
      · nlinarith [Real.pi_pos, hy0]
      · nlinarith [hy0]
    simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hle hsin
  have hA2 : (∫ x in Real.pi..2 * Real.pi, -(Real.sinc x))
      ≤ ((35441:ℝ)/1000000 + (86569:ℝ)/1000000 + (107108:ℝ)/1000000
        + (99889:ℝ)/1000000 + (71798:ℝ)/1000000 + (32392:ℝ)/1000000) + (1:ℝ)/40 := by
    calc
      (∫ x in Real.pi..2 * Real.pi, -(Real.sinc x))
          = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := hA
      _ ≤ ∫ y in (0:ℝ)..Real.pi, Real.sin y / ((6283:ℝ)/2000 + y) := hcπ
      _ ≤ ((35441:ℝ)/1000000 + (86569:ℝ)/1000000 + (107108:ℝ)/1000000
        + (99889:ℝ)/1000000 + (71798:ℝ)/1000000 + (32392:ℝ)/1000000) + (1:ℝ)/40 := hM
  have hrel : ∫ x in Real.pi..2 * Real.pi, Real.sinc x
      = -(∫ x in Real.pi..2 * Real.pi, -(Real.sinc x)) := by
    rw [intervalIntegral.integral_neg]
    ring
  rw [hrel]
  linarith

/-! ## The three main bounds -/

theorem int_0_2pi_ge : (4 / 3 : ℝ) ≤ ∫ x in (0 : ℝ)..2 * Real.pi, Real.sinc x := by
  have hA := int_add_adj (f := Real.sinc) (by norm_num : (0:ℝ) ≤ 3)
    (by linarith [Real.pi_gt_three] : (3:ℝ) ≤ Real.pi) Real.continuous_sinc
  have hB := int_add_adj (f := Real.sinc) (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi)
    (by nlinarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi) Real.continuous_sinc
  rw [← hB, ← hA]
  have hP := int_0_3_sinc_ge
  have hMid : (0:ℝ) ≤ ∫ x in (3:ℝ)..Real.pi, Real.sinc x := by
    exact int_sinc_nonneg 3 Real.pi (by linarith [Real.pi_gt_three]) (by norm_num) (le_rfl)
  have hN := int_pi_2pi_ge_negS
  have hm : (4/3:ℝ) ≤
      ((4930:ℝ)/10000 + (438184:ℝ)/1000000 + (374838:ℝ)/1000000 + (279491:ℝ)/1000000
        + (172670:ℝ)/1000000 + (70011:ℝ)/1000000)
      - (((433197:ℝ)/1000000) + (1:ℝ)/40) := by norm_num
  nlinarith

/-- antiderivative `G` of `1 - x²/6 + x⁴/120`. -/
private lemma dG (u : ℝ) : HasDerivAt (fun t : ℝ => t - t^3/18 + t^5/600)
    (1 - u^2/6 + u^4/120) u := by
  have h0 : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id u
  have h1 : HasDerivAt (fun t : ℝ => t^3/18) (3*u^2/18) u := by
    simpa using (hasDerivAt_pow 3 u).div_const 18
  have h2 : HasDerivAt (fun t : ℝ => t^5/600) (5*u^4/600) u := by
    simpa using (hasDerivAt_pow 5 u).div_const 600
  exact (((h0.sub h1).add h2)).congr_deriv (by ring)

/-- `G` is monotone (its derivative is `1/6 + (x²-10)²/120 ≥ 0`). -/
private lemma G_mono : Monotone (fun t : ℝ => t - t^3/18 + t^5/600) := by
  apply monotone_of_deriv_nonneg
  · intro x
    fun_prop
  · intro x
    have hG' : HasDerivAt (fun t : ℝ => t - t^3/18 + t^5/600)
        (1/6 + (x^2 - 10)^2/120) x := by
      have hd := dG x
      refine hd.congr_deriv ?_
      ring
    have hv : deriv (fun t : ℝ => t - t^3/18 + t^5/600) x = 1/6 + (x^2 - 10)^2/120 := hG'.deriv
    rw [hv]
    positivity

theorem int_0_pi_le : (∫ x in (0 : ℝ)..Real.pi, Real.sinc x) ≤ 2 := by
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      Real.sinc x ≤ 1 - x^2/6 + x^4/120 := by
    intro x hx
    by_cases h0 : x = 0
    · subst x
      norm_num [Real.sinc_zero]
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
      have hsin := sin_le_1 x hx.1
      rw [Real.sinc_of_ne_zero h0]
      have hdiv : Real.sin x / x ≤ (x - x^3/6 + x^5/120) / x := by
        exact div_le_div_of_nonneg_right hsin (le_of_lt hxpos)
      calc
        Real.sin x / x ≤ (x - x^3/6 + x^5/120) / x := hdiv
        _ = 1 - x^2/6 + x^4/120 := by
          field_simp [h0]
  have hcont : Continuous (fun x : ℝ => 1 - x^2/6 + x^4/120) := by fun_prop
  have hmono : (∫ x in (0:ℝ)..Real.pi, Real.sinc x)
      ≤ ∫ x in (0:ℝ)..Real.pi, (1 - x^2/6 + x^4/120) := by
    refine intervalIntegral.integral_mono_on (by positivity) (Real.continuous_sinc.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) hpt
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) Real.pi,
      HasDerivAt (fun t : ℝ => t - t^3/18 + t^5/600) (1 - y^2/6 + y^4/120) y := by
    intro y hy
    exact dG y
  have hval := int_zero_eq_sub (by positivity : (0:ℝ) ≤ Real.pi) hcont hderiv
  rw [hval] at hmono
  have hleG : (fun t : ℝ => t - t^3/18 + t^5/600) Real.pi
      ≤ (fun t : ℝ => t - t^3/18 + t^5/600) ((315:ℝ)/100) := by
    exact G_mono (by nlinarith [Real.pi_lt_d2])
  have hnum : (fun t : ℝ => t - t^3/18 + t^5/600) ((315:ℝ)/100) ≤ 2 := by norm_num
  nlinarith

theorem int_pi_2pi_ge : -1 ≤ ∫ x in Real.pi..2 * Real.pi, Real.sinc x := by
  have hN := int_pi_2pi_ge_negS
  have hnum : -(((433197:ℝ)/1000000) + (1:ℝ)/40) ≥ -1 := by norm_num
  linarith


end SincNum
end Submission
