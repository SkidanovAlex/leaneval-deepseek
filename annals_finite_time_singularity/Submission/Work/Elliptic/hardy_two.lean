import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.hardy_two_regular
import Submission.Work.Elliptic.hardy_two_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- **Lemma `HardyInequality2` of Elgindi (Annals 194 (3), 2021).**

For `f : ℝ → ℝ` of class `C²` on `[0, π/2]` with `f 0 = f (π/2) = 0`,

`∫_0^{π/2} (∂_θ (f / sin 2θ))² ≤ 10 ∫_0^{π/2} (f'')²`.

The proof is the exact integration by parts recorded in `HardyTwoDefs`: with
`u = f / sin(2θ)` one has `f'' = sin(2θ) u'' + 4 cos(2θ) u' - 4 sin(2θ) u`, and then

`10 (f'')² - (u')² - htNN = (htPP)'`,

where `htNN ≥ 0` pointwise and `htPP` vanishes at `0` and `π/2`.  Integrating over
`[0,π/2]` (the Fundamental Theorem of Calculus, valid because `htPP` is continuous on
`[0,π/2]` and `htEE` is interval-integrable) gives `∫ (u')² = 10 ∫ (f'')² - ∫ htNN`,
whence the bound. -/
theorem hardy_two (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => f θ' / Real.sin (2 * θ')) θ) ^ 2
      ≤ 10 * ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => deriv f θ') θ) ^ 2 := by
  obtain ⟨hcont, hIntEE, hIntNN, hIntd2f⟩ := hardy_two_regular f hf h0 h1
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  -- The Fundamental Theorem of Calculus: `∫_0^{π/2} htEE = htPP(π/2) - htPP(0) = 0`.
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2), htEE f θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
        (fun x hx => hardy_two_hasDerivAt f hf x hx) hIntEE,
      htPP_pi2 f, htPP_zero f, sub_zero]
  -- Both integrals over `Iθ = Icc 0 (π/2)` are interval integrals over `0..π/2`.
  have hconv1 : ∫ θ in Work.Spaces.Iθ, (deriv (htU f) θ) ^ 2
      = ∫ θ in (0 : ℝ)..(π / 2), (deriv (htU f) θ) ^ 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  have hconv2 : (∫ θ in (0 : ℝ)..(π / 2), (deriv (deriv f) θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  have hIntd2f10 : IntervalIntegrable (fun θ => 10 * (deriv (deriv f) θ) ^ 2) volume 0 (π / 2) :=
    hIntd2f.const_mul 10
  have hIntsub : IntervalIntegrable
      (fun θ => 10 * (deriv (deriv f) θ) ^ 2 - htNN f θ) volume 0 (π / 2) :=
    hIntd2f10.sub hIntNN
  calc ∫ θ in Work.Spaces.Iθ, (deriv (htU f) θ) ^ 2
      = ∫ θ in (0 : ℝ)..(π / 2), (deriv (htU f) θ) ^ 2 := hconv1
    _ = ∫ θ in (0 : ℝ)..(π / 2),
          (10 * (deriv (deriv f) θ) ^ 2 - htNN f θ - htEE f θ) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact ht_sq_eq f θ
    _ = (∫ θ in (0 : ℝ)..(π / 2), (10 * (deriv (deriv f) θ) ^ 2 - htNN f θ))
          - (∫ θ in (0 : ℝ)..(π / 2), htEE f θ) := by
          rw [intervalIntegral.integral_sub hIntsub hIntEE]
    _ = (∫ θ in (0 : ℝ)..(π / 2), (10 * (deriv (deriv f) θ) ^ 2 - htNN f θ)) := by
          rw [hFTC, sub_zero]
    _ = 10 * (∫ θ in (0 : ℝ)..(π / 2), (deriv (deriv f) θ) ^ 2)
          - (∫ θ in (0 : ℝ)..(π / 2), htNN f θ) := by
          rw [intervalIntegral.integral_sub hIntd2f10 hIntNN,
            intervalIntegral.integral_const_mul]
    _ ≤ 10 * (∫ θ in (0 : ℝ)..(π / 2), (deriv (deriv f) θ) ^ 2) := by
          have hnn : 0 ≤ ∫ θ in (0 : ℝ)..(π / 2), htNN f θ :=
            intervalIntegral.integral_nonneg hle (fun u _ => htNN_nonneg f u)
          linarith
    _ = 10 * ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 := by rw [hconv2]

end Work.Elliptic
