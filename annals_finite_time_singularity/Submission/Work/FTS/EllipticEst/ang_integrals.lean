import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The three elementary angular integrals

The set `Work.Spaces.Iθ` is `Set.Icc 0 (π/2)`, which differs from the interval `0..π/2` by the
null set `{0}` only; we first evaluate everything as an interval integral and transfer at the end.

The evaluations are

* `∫_0^{π/2} sin²(2θ) dθ = π/4`, via `sin²(2θ) = 4 sin²θ cos²θ` and
  `∫_0^{π/2} sin²θ cos²θ = (π/2)/8 = π/16`;
* `∫_0^{π/2} sin²θ cos⁴θ dθ = π/32`, via `sin²θ cos⁴θ = (1/8) sin²(2θ) (1 + cos 2θ)` together with
  the first evaluation and `∫_0^{π/2} sin²(2θ) cos(2θ) dθ = 0`;
* `∫_0^{π/2} sin θ cos²θ · sin(2θ) dθ = 4/15`, the substitution `u = sin θ`
  (`Work.Elliptic.integral_sin_two_mul_sinCos2`). -/

/-- A set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
private lemma setIntegral_Iθ_eq (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- `∫_0^{π/2} sin²(2θ) dθ = π/4`. -/
private lemma integral_sin_two_sq_pi2 :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2) = Real.pi / 4 := by
  have hpt : ∀ θ : ℝ, (Real.sin (2 * θ)) ^ 2 = 4 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) := by
    intro θ; rw [Real.sin_two_mul]; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_cos_sq]
  rw [show (4 : ℝ) * (π / 2) = 2 * π by ring, show (4 : ℝ) * 0 = 0 by ring]
  simp
  ring

/-- `∫_0^{π/2} sin²(2θ) cos(2θ) dθ = 0`: substitute `u = 2θ` and use
`∫_0^π sin²u cos u du = (sin³π - sin³0)/3 = 0`. -/
private lemma integral_sin_two_sq_mul_cos_two :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => Real.sin u ^ 2 * Real.cos u) (c := 2) (by norm_num)]
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * (π / 2) = π by ring]
  rw [integral_sin_sq_mul_cos]
  simp

/-- `∫_0^{π/2} sin²θ cos⁴θ dθ = π/32`. -/
private lemma integral_sinCos2_sq_pi2 :
    (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2) = Real.pi / 32 := by
  have hpt : ∀ θ : ℝ, (Work.Elliptic.sinCos2 θ) ^ 2
      = (1 / 8) * ((Real.sin (2 * θ)) ^ 2 + (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) := by
    intro θ
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul, Real.cos_two_mul]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)).intervalIntegrable _ _),
    integral_sin_two_sq_pi2, integral_sin_two_sq_mul_cos_two]
  ring

/-- The elementary angular integrals and the numerical inequality used by the Cauchy–Schwarz
bound on the first sine coefficient of a function orthogonal to `sinθcos²θ`
(`∫ sin²2θ = π/4`, `∫ sin²θcos⁴θ = π/32`, `∫ sinθcos²θ sin2θ = 4/15`, and
`π/32 - (4/15)²/(π/4) ≤ (1/4)(π/32)`, i.e. `675 π² ≤ 8192`). -/
theorem ang_integrals :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ 2) = Real.pi / 4 ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) = Real.pi / 32 ∧
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ)) = 4 / 15 ∧
    ((Real.pi / 32 : ℝ) - (4 / 15) ^ 2 / (Real.pi / 4) ≤ (1 / 4) * (Real.pi / 32)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [setIntegral_Iθ_eq]; exact integral_sin_two_sq_pi2
  · rw [setIntegral_Iθ_eq]; exact integral_sinCos2_sq_pi2
  · rw [← Work.Elliptic.integral_sin_two_mul_sinCos2]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
  · -- `π/32 - (4/15)²/(π/4) ≤ (1/4)(π/32)` is `675 π² ≤ 8192`, and `π < 3.15`.
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have key : (675 : ℝ) * Real.pi ^ 2 ≤ 8192 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h2 : (1 : ℝ) / 4 * (Real.pi / 32) - (Real.pi / 32 - (4 / 15) ^ 2 / (Real.pi / 4))
        = (8192 - 675 * Real.pi ^ 2) / (28800 * Real.pi) := by
      field_simp
      ring
    have h3 : (0 : ℝ) ≤ (1 : ℝ) / 4 * (Real.pi / 32)
        - (Real.pi / 32 - (4 / 15) ^ 2 / (Real.pi / 4)) := by
      rw [h2]
      exact div_nonneg (by linarith [key]) (by positivity)
    linarith [h3]

end Work.FTS.EllipticEst
