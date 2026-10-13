import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory

/-!
Elementary angular facts on `Iθ = [0,π/2]`, `K θ = 3 sin θ cos²θ`, `qfun θ = cos 2θ - 1/3`.

The proofs are direct computations:
* `K ≥ 0` and `cos ≥ 0` on `Iθ` are pointwise positivity;
* `K θ ≤ 2 cos θ` follows from `3 sin θ cos θ ≤ 3/2 ≤ 2` and `cos θ ≥ 0`;
* `∫_{Iθ} cos = 1` is the FTC with primitive `sin`, `∫_{Iθ} K = 1` the FTC with
  primitive `-cos³`;
* `|qfun| ≤ 4/3` is `|cos 2θ - 1/3| ≤ 4/3` from `-1 ≤ cos ≤ 1`;
* `K θ = (3/2) cos θ sin (2θ)` is `Real.sin_two_mul` and `ring`;
* `|sin (2θ)| ≤ 2` is `|sin| ≤ 1`.
-/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral from `0` to `π/2`. -/
private lemma Iθ_setIntegral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `cos` is nonnegative on `Iθ`. -/
private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩

/-- `sin` is nonnegative on `Iθ`. -/
private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩

/-- `3 sin θ cos θ ≤ 2` for all `θ` (the maximum of `3 sin θ cos θ` is `3/2`). -/
private lemma three_sin_cos_le_two (θ : ℝ) : 3 * Real.sin θ * Real.cos θ ≤ 2 := by
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2 ≤ 1 :=
    calc 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2
        = 1 - (Real.sin θ ^ 2 - Real.cos θ ^ 2) ^ 2 := by
          nlinarith [hsq]
      _ ≤ 1 := by linarith [sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2)]
  have h9 : (3 * Real.sin θ * Real.cos θ) ^ 2 ≤ 4 := by nlinarith [h4]
  nlinarith [h9, sq_nonneg (3 * Real.sin θ * Real.cos θ - 2)]

/-- The angular weight `K` is continuous. -/
private lemma continuous_K : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  rw [show (fun θ : ℝ => Work.Spaces.K θ)
        = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from by
      funext θ; rw [Work.Spaces.K]]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- `∫_{Iθ} cos θ = 1` (FTC with primitive `sin`). -/
private lemma integral_cos_Iθ : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
  rw [Iθ_setIntegral_eq_intervalIntegral]
  have h : (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ)
      = Real.sin (Real.pi / 2) - Real.sin 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x)
      (Real.continuous_cos.intervalIntegrable _ _)
  rw [h, Real.sin_pi_div_two, Real.sin_zero, sub_zero]

/-- `d/dθ (-cos³θ) = K θ`, so `-cos³` is a primitive of `K`. -/
private lemma hasDerivAt_neg_cos_cube (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.cos t) ^ 3) (Work.Spaces.K x) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos x ^ 2 * -Real.sin x) x :=
    (Real.hasDerivAt_cos x).pow 3
  convert h1.neg using 1
  rw [Work.Spaces.K]; ring

/-- `∫_{Iθ} K θ = 1` (FTC with primitive `-cos³`). -/
private lemma integral_K_Iθ : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  rw [Iθ_setIntegral_eq_intervalIntegral]
  have hInt : (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ)
      = (fun t : ℝ => -(Real.cos t) ^ 3) (Real.pi / 2)
        - (fun t : ℝ => -(Real.cos t) ^ 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -(Real.cos t) ^ 3)
      (f' := fun t : ℝ => Work.Spaces.K t) (fun x _ => hasDerivAt_neg_cos_cube x)
      (continuous_K.intervalIntegrable _ _)
  rw [hInt]
  norm_num [Real.cos_pi_div_two, Real.cos_zero]

theorem AngFacts :
    (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Spaces.K θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ ≤ 2 * Real.cos θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.cos θ) ∧
    (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 ∧
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 ∧
    (∀ θ : ℝ, |Work.Spaces.qfun θ| ≤ 4 / 3) ∧
    (∀ θ : ℝ, Work.Spaces.K θ = 3 / 2 * Real.cos θ * Real.sin (2 * θ)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ)| ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K ≥ 0` on `Iθ`
    intro θ hθ
    have hs := sin_nonneg_of_mem_Iθ hθ
    have hc : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    rw [Work.Spaces.K]
    exact mul_nonneg (mul_nonneg (by norm_num) hs) hc
  · -- `K θ ≤ 2 cos θ` on `Iθ`
    intro θ hθ
    have hc0 := cos_nonneg_of_mem_Iθ hθ
    have hsc := three_sin_cos_le_two θ
    rw [Work.Spaces.K]
    nlinarith [mul_le_mul_of_nonneg_right hsc hc0]
  · exact fun θ hθ => cos_nonneg_of_mem_Iθ hθ
  · exact integral_cos_Iθ
  · exact integral_K_Iθ
  · -- `|qfun θ| ≤ 4/3`
    intro θ
    rw [Work.Spaces.qfun_apply, abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
  · -- `K θ = (3/2) cos θ sin (2θ)`
    intro θ
    rw [Work.Spaces.K, Real.sin_two_mul]
    ring
  · -- `|sin (2θ)| ≤ 2` on `Iθ`
    intro θ _
    linarith [Real.abs_sin_le_one (2 * θ)]

end Work.FTS.StrongEps.E5Aux2
