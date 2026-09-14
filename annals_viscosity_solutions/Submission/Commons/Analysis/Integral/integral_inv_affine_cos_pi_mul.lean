import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Classical integral of `1/(A + B·cos)` over one half-period

For `0 < B < A`:

    ∫ u in 0..1, 1/(A + B·cos(π·u)) du  =  1/√(A² − B²)

Equivalently, after the change of variables `v = π·u`,

    ∫ v in 0..π, 1/(A + B·cos v) dv  =  π / √(A² − B²).

## Proof outline (smooth antiderivative, no improper integrals)

For `0 < B < A`, the function

    G(v) = arccos((B + A·cos v)/(A + B·cos v)) / √(A² − B²)

is `C¹` on `[0, π]` (the denominator `A + B·cos v ≥ A − B > 0` and the argument
of `arccos` stays in `[−1,1]`), with derivative `1/(A + B·cos v)` on `(0, π)`
(because `A + B·cos v` is bounded away from 0).  Hence

    ∫ v in 0..π, 1/(A + B·cos v) dv = G(π) − G(0)
        = (arccos(−1) − arccos(1))/√(A²−B²) = (π − 0)/√(A²−B²).

Use `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` with this antiderivative, and
`Real.hasDerivAt_arccos` / chain rule for the derivative step.  The final affine
version follows from the substitution `v = π·u`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Commons.Analysis.Integral

/-! ## Elementary bounds and algebraic identities -/

/-- `A + B·cos v` is positive for all `v` when `0 < B < A`. -/
lemma affine_cos_denom_pos {A B : ℝ} (hBpos : 0 < B) (hBA : B < A) (v : ℝ) :
    0 < A + B * Real.cos v := by
  have hBcos : -B ≤ B * Real.cos v := by
    have hle := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos v) hBpos.le
    nlinarith
  nlinarith

/-- On `(0,π)` the arccos argument `(B + A·cos v)/(A + B·cos v)` lies strictly in `(-1,1)`:
upper bound. -/
lemma affine_cos_arg_lt_one {A B v : ℝ} (hBpos : 0 < B) (hBA : B < A)
    (hv0 : 0 < v) (hvπ : v < Real.pi) :
    (B + A * Real.cos v) / (A + B * Real.cos v) < 1 := by
  have hden : 0 < A + B * Real.cos v := affine_cos_denom_pos hBpos hBA v
  have hAB : 0 < A - B := sub_pos.mpr hBA
  have hcv1 : Real.cos v < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_rfl : (0 : ℝ) ≤ 0) hvπ.le hv0
  have hprod : 0 < (A - B) * (1 - Real.cos v) := mul_pos hAB (sub_pos.mpr hcv1)
  rw [div_lt_iff₀ hden]
  nlinarith

/-- On `(0,π)` the arccos argument lies strictly in `(-1,1)`: lower bound. -/
lemma affine_cos_arg_gt_neg_one {A B v : ℝ} (hBpos : 0 < B) (hBA : B < A)
    (hv0 : 0 < v) (hvπ : v < Real.pi) :
    -1 < (B + A * Real.cos v) / (A + B * Real.cos v) := by
  have hden : 0 < A + B * Real.cos v := affine_cos_denom_pos hBpos hBA v
  have hA : 0 < A := lt_trans hBpos hBA
  have hcosg : -1 < Real.cos v := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hv0.le le_rfl hvπ
    simpa using h
  have hprod : 0 < (A + B) * (1 + Real.cos v) :=
    mul_pos (add_pos hA hBpos) (by linarith)
  rw [lt_div_iff₀ hden]
  nlinarith

/-- Identity `1 - x(v)^2 = (A²−B²)·sin²v/(A+B·cos v)²`. -/
lemma affine_cos_one_sub_sq {A B v : ℝ} :
    (A + B * Real.cos v) ^ 2 - (B + A * Real.cos v) ^ 2 =
      (A ^ 2 - B ^ 2) * (Real.sin v) ^ 2 := by
  have hsin : (Real.sin v) ^ 2 = 1 - (Real.cos v) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq v
    nlinarith
  rw [hsin]
  ring

/-- Square root of `1 - x(v)^2` where `x(v) = (B + A·cos v)/(A + B·cos v)`. -/
lemma affine_cos_sqrt_arg {A B v : ℝ} (hBpos : 0 < B) (hBA : B < A)
    (hv0 : 0 < v) (hvπ : v < Real.pi) :
    Real.sqrt (1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2) =
      Real.sqrt (A ^ 2 - B ^ 2) * Real.sin v / (A + B * Real.cos v) := by
  have hden : A + B * Real.cos v ≠ 0 := (affine_cos_denom_pos hBpos hBA v).ne'
  have hsin : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 hvπ
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by
    nlinarith [sq_sub_sq A B]
  have hsq : 1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2 =
      (A ^ 2 - B ^ 2) * (Real.sin v) ^ 2 / (A + B * Real.cos v) ^ 2 := by
    calc
      1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2
          = (((A + B * Real.cos v) ^ 2 - (B + A * Real.cos v) ^ 2) /
              (A + B * Real.cos v) ^ 2) := by
            field_simp [hden]
      _ = (A ^ 2 - B ^ 2) * (Real.sin v) ^ 2 / (A + B * Real.cos v) ^ 2 := by
            rw [affine_cos_one_sub_sq (A := A) (B := B) (v := v)]
  calc
    Real.sqrt (1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2)
        = Real.sqrt ((A ^ 2 - B ^ 2) * (Real.sin v) ^ 2 /
            (A + B * Real.cos v) ^ 2) := by rw [hsq]
    _ = Real.sqrt ((A ^ 2 - B ^ 2) * (Real.sin v) ^ 2) /
          Real.sqrt ((A + B * Real.cos v) ^ 2) := by
        rw [Real.sqrt_div (mul_nonneg hA2B2.le (sq_nonneg _))]
    _ = Real.sqrt (A ^ 2 - B ^ 2) * Real.sin v /
          (A + B * Real.cos v) := by
        rw [Real.sqrt_mul hA2B2.le, Real.sqrt_sq_eq_abs, abs_of_pos hsin]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (affine_cos_denom_pos hBpos hBA v)]

lemma chain_value_clean {A B v : ℝ} (hBpos : 0 < B) (hBA : B < A)
    (hv0 : 0 < v) (hvπ : v < Real.pi) :
    -(1 / Real.sqrt (1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2)) *
        (-(A ^ 2 - B ^ 2) * Real.sin v / (A + B * Real.cos v) ^ 2) =
      Real.sqrt (A ^ 2 - B ^ 2) / (A + B * Real.cos v) := by
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by
    nlinarith [sq_sub_sq A B]
  have hden : A + B * Real.cos v ≠ 0 := (affine_cos_denom_pos hBpos hBA v).ne'
  have hsin : Real.sin v ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hv0 hvπ).ne'
  have hc : Real.sqrt (A ^ 2 - B ^ 2) ≠ 0 := (Real.sqrt_ne_zero').2 hA2B2
  have hsqrt : Real.sqrt (1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2) =
      Real.sqrt (A ^ 2 - B ^ 2) * Real.sin v / (A + B * Real.cos v) :=
    affine_cos_sqrt_arg hBpos hBA hv0 hvπ
  have hsqu : (Real.sqrt (A ^ 2 - B ^ 2)) ^ 2 = A ^ 2 - B ^ 2 := Real.sq_sqrt hA2B2.le
  rw [hsqrt]
  conv_lhs =>
    rw [← hsqu]
    rw [Real.sqrt_sq (Real.sqrt_nonneg (A ^ 2 - B ^ 2))]
  field_simp [hc, hsin, hden]

/-- The antiderivative `arccos((B + A·cos v)/(A + B·cos v)) / √(A²−B²)` has derivative
`(A + B·cos v)⁻¹` on `(0,π)`. -/
lemma hasDerivAt_inv_affine_cos_aux {A B v : ℝ} (hBpos : 0 < B) (hBA : B < A)
    (hv0 : 0 < v) (hvπ : v < Real.pi) :
    HasDerivAt
      (fun u : ℝ =>
        Real.arccos ((B + A * Real.cos u) / (A + B * Real.cos u)) /
          Real.sqrt (A ^ 2 - B ^ 2))
      ((A + B * Real.cos v)⁻¹) v := by
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by
    nlinarith [sq_sub_sq A B]
  have hden_ne : A + B * Real.cos v ≠ 0 := (affine_cos_denom_pos hBpos hBA v).ne'
  have hc : Real.sqrt (A ^ 2 - B ^ 2) ≠ 0 := (Real.sqrt_ne_zero').2 hA2B2
  let num : ℝ → ℝ := fun u => B + A * Real.cos u
  let den : ℝ → ℝ := fun u => A + B * Real.cos u
  let x : ℝ → ℝ := fun u => num u / den u
  have hxarg_lt : x v < 1 := by
    dsimp [x, num, den]
    exact affine_cos_arg_lt_one hBpos hBA hv0 hvπ
  have hxarg_gt : -1 < x v := by
    dsimp [x, num, den]
    exact affine_cos_arg_gt_neg_one hBpos hBA hv0 hvπ
  have hxv1 : x v ≠ 1 := ne_of_lt hxarg_lt
  have hxvm1 : x v ≠ -1 := ne_of_gt hxarg_gt
  have hnum_der : HasDerivAt num (A * (-Real.sin v)) v := by
    dsimp [num]
    have h2 : HasDerivAt (fun u : ℝ => A * Real.cos u) (A * (-Real.sin v)) v := by
      simpa using (Real.hasDerivAt_cos v).const_mul A
    simpa using h2.const_add B
  have hden_der : HasDerivAt den (B * (-Real.sin v)) v := by
    dsimp [den]
    have h2 : HasDerivAt (fun u : ℝ => B * Real.cos u) (B * (-Real.sin v)) v := by
      simpa using (Real.hasDerivAt_cos v).const_mul B
    simpa using h2.const_add A
  have hx_der : HasDerivAt x
      ((A * (-Real.sin v) * den v - num v * (B * (-Real.sin v))) / den v ^ 2) v := by
    dsimp [x]
    exact hnum_der.div hden_der hden_ne
  have hx_clean : HasDerivAt x
      (-(A ^ 2 - B ^ 2) * Real.sin v / (A + B * Real.cos v) ^ 2) v := by
    refine hx_der.congr_deriv ?_
    dsimp [num, den]
    field_simp [hden_ne]
    ring
  have harccos_der : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - (x v) ^ 2))) (x v) :=
    Real.hasDerivAt_arccos hxvm1 hxv1
  have hcomp : HasDerivAt (Real.arccos ∘ x)
      (-(1 / Real.sqrt (1 - (x v) ^ 2)) * (-(A ^ 2 - B ^ 2) * Real.sin v /
        (A + B * Real.cos v) ^ 2)) v := by
    simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using harccos_der.comp v hx_clean
  have hF : HasDerivAt (fun u : ℝ => Real.arccos (x u) / Real.sqrt (A ^ 2 - B ^ 2))
      (-(1 / Real.sqrt (1 - (x v) ^ 2)) * (-(A ^ 2 - B ^ 2) * Real.sin v /
        (A + B * Real.cos v) ^ 2) / Real.sqrt (A ^ 2 - B ^ 2)) v := by
    simpa using hcomp.div_const (Real.sqrt (A ^ 2 - B ^ 2))
  have hclean : -(1 / Real.sqrt (1 - (x v) ^ 2)) * (-(A ^ 2 - B ^ 2) * Real.sin v /
        (A + B * Real.cos v) ^ 2) / Real.sqrt (A ^ 2 - B ^ 2) = (A + B * Real.cos v)⁻¹ := by
    dsimp [x]
    calc
      -(1 / Real.sqrt (1 - ((B + A * Real.cos v) / (A + B * Real.cos v)) ^ 2)) *
          (-(A ^ 2 - B ^ 2) * Real.sin v / (A + B * Real.cos v) ^ 2) /
            Real.sqrt (A ^ 2 - B ^ 2)
          = Real.sqrt (A ^ 2 - B ^ 2) / (A + B * Real.cos v) /
              Real.sqrt (A ^ 2 - B ^ 2) := by
            rw [chain_value_clean hBpos hBA hv0 hvπ]
      _ = (A + B * Real.cos v)⁻¹ := by
            field_simp [hc, hden_ne]
  exact hF.congr_deriv hclean

lemma integral_inv_affine_cos {A B : ℝ} (hBpos : 0 < B) (hBA : B < A) :
    (∫ v in (0 : ℝ)..Real.pi, (A + B * Real.cos v)⁻¹) =
      Real.pi / Real.sqrt (A ^ 2 - B ^ 2) := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by
    nlinarith [sq_sub_sq A B]
  have hc : Real.sqrt (A ^ 2 - B ^ 2) ≠ 0 := (Real.sqrt_ne_zero').2 hA2B2
  -- the integrand is continuous, hence integrable on [0, π]
  have hcont_inv : Continuous fun v : ℝ => (A + B * Real.cos v)⁻¹ := by
    refine Continuous.inv₀ ?_ (fun v => (affine_cos_denom_pos hBpos hBA v).ne')
    fun_prop
  have hint : IntervalIntegrable (fun v : ℝ => (A + B * Real.cos v)⁻¹) volume 0 Real.pi :=
    hcont_inv.continuousOn.intervalIntegrable_of_Icc hpi
  -- the antiderivative is continuous on [0, π]
  have hcont_arg : Continuous fun v : ℝ =>
      (B + A * Real.cos v) / (A + B * Real.cos v) := by
    refine (by fun_prop : Continuous fun v : ℝ => B + A * Real.cos v).div
      (by fun_prop : Continuous fun v : ℝ => A + B * Real.cos v)
      (fun v => (affine_cos_denom_pos hBpos hBA v).ne')
  have hcont_F : Continuous fun v : ℝ =>
      Real.arccos ((B + A * Real.cos v) / (A + B * Real.cos v)) /
        Real.sqrt (A ^ 2 - B ^ 2) := by
    have h1 : Continuous fun v : ℝ =>
        Real.arccos ((B + A * Real.cos v) / (A + B * Real.cos v)) :=
      Real.continuous_arccos.comp hcont_arg
    exact h1.div continuous_const (fun _ => hc)
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt
        (fun u : ℝ =>
          Real.arccos ((B + A * Real.cos u) / (A + B * Real.cos u)) /
            Real.sqrt (A ^ 2 - B ^ 2))
        ((A + B * Real.cos v)⁻¹) v :=
    fun v hv => hasDerivAt_inv_affine_cos_aux hBpos hBA hv.1 hv.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpi hcont_F.continuousOn hderiv hint
  -- endpoint values of the antiderivative
  have hxpi : (B + A * Real.cos Real.pi) / (A + B * Real.cos Real.pi) = -1 := by
    have hd : A + B * Real.cos Real.pi ≠ 0 :=
      (affine_cos_denom_pos hBpos hBA Real.pi).ne'
    have hnum : B + A * Real.cos Real.pi = -(A + B * Real.cos Real.pi) := by
      rw [Real.cos_pi]
      ring
    rw [hnum]
    rw [neg_div, div_self hd]
  have hx0 : (B + A * Real.cos 0) / (A + B * Real.cos 0) = 1 := by
    rw [Real.cos_zero]
    field_simp [ne_of_gt (add_pos (lt_trans hBpos hBA) hBpos)]
    ring
  have hFpi : Real.arccos ((B + A * Real.cos Real.pi) / (A + B * Real.cos Real.pi)) /
        Real.sqrt (A ^ 2 - B ^ 2) = Real.pi / Real.sqrt (A ^ 2 - B ^ 2) := by
    rw [hxpi, Real.arccos_neg_one]
  have hF0 : Real.arccos ((B + A * Real.cos 0) / (A + B * Real.cos 0)) /
        Real.sqrt (A ^ 2 - B ^ 2) = 0 := by
    rw [hx0, Real.arccos_one]
    simp
  calc
    (∫ v in (0 : ℝ)..Real.pi, (A + B * Real.cos v)⁻¹)
        = Real.arccos ((B + A * Real.cos Real.pi) / (A + B * Real.cos Real.pi)) /
            Real.sqrt (A ^ 2 - B ^ 2) -
          Real.arccos ((B + A * Real.cos 0) / (A + B * Real.cos 0)) /
            Real.sqrt (A ^ 2 - B ^ 2) := by
          simpa using hFTC
    _ = Real.pi / Real.sqrt (A ^ 2 - B ^ 2) := by
          rw [hFpi, hF0]
          simp

theorem integral_inv_affine_cos_pi_mul {A B : ℝ} (hBpos : 0 < B) (hBA : B < A) :
    (∫ u in (0 : ℝ)..1, (A + B * Real.cos (Real.pi * u))⁻¹) =
      (Real.sqrt (A ^ 2 - B ^ 2))⁻¹ := by
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by
    nlinarith [sq_sub_sq A B]
  have hc : Real.sqrt (A ^ 2 - B ^ 2) ≠ 0 := (Real.sqrt_ne_zero').2 hA2B2
  calc
    (∫ u in (0 : ℝ)..1, (A + B * Real.cos (Real.pi * u))⁻¹)
        = Real.pi⁻¹ * (∫ v in (0 : ℝ)..Real.pi, (A + B * Real.cos v)⁻¹) := by
          rw [intervalIntegral.integral_comp_mul_left
            (f := fun v : ℝ => (A + B * Real.cos v)⁻¹) hpi_ne]
          simp [smul_eq_mul]
    _ = (Real.sqrt (A ^ 2 - B ^ 2))⁻¹ := by
          rw [integral_inv_affine_cos hBpos hBA]
          field_simp [hpi_ne, hc]

end Commons.Analysis.Integral
