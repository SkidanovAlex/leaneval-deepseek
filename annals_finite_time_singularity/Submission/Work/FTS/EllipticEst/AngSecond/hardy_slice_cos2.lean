import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The angular Hardy inequality with the `cos²(2θ)` factor, at the paper's exponent.**

There is `C > 0` such that for every `f : ℝ → ℝ` of class `C¹` on `[0,π/2]` with
`f 0 = f (π/2) = 0`,

  `∫_θ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1/(1+η)²) ∫_θ (f')² sin(2θ)^{-η} + C ∫_θ f² sin(2θ)^{-η}`,

`η = Work.Spaces.eta = 99/100`, all integrals over `Work.Spaces.Iθ`.

Route: `cos²(2θ) ≤ 1` pointwise, so the left-hand side is at most
`∫_θ f² sin(2θ)^{-(2+η)}`, which is exactly the left-hand side of the proved
`Work.FTS.EllipticEst.hardy_shift_two_same_weight` with `η = Work.Spaces.eta`
(`0 ≤ eta`, `eta < 1`), whose right-hand side is
`(1/(1+η)²) ∫_θ (f')² sin(2θ)^{-η} + C₀ ∫_θ f² sin(2θ)^{-η}`.
(The same-weight correction term is what makes the constant usable.) -/
theorem hardy_slice_cos2 : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
    (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (1 / (1 + Work.Spaces.eta) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + C * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.hardy_shift_two_same_weight Work.Spaces.eta
      Work.Spaces.eta_nonneg Work.Spaces.eta_lt_one
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  -- Integrability of the un-truncated left-hand integrand (already in the repository)
  obtain ⟨hI1, -, -, -, -⟩ :=
    Work.Elliptic.sin_weight_integrable Work.Spaces.eta_nonneg Work.Spaces.eta_lt_one hf hf0 hfpi
  have hInt : IntegrableOn
      (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      Work.Spaces.Iθ volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2).mp hI1
  -- Step 1: `cos²(2θ) ≤ 1` drops out of the left-hand side
  have hstep1 : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (hsin_nn θ hθ) _)
    · exact hInt
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hcos : Real.cos (2 * θ) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
      have hs : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
        Real.rpow_nonneg (hsin_nn θ hθ) _
      calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
          ≤ f θ ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcos (sq_nonneg _)) hs
        _ = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by ring
  -- Step 2: the same-weight Hardy inequality, in the `rpow`-negative notation
  have h1 : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show f θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)
        = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) (2 + Work.Spaces.eta)]
  have h2 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
        = (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) (Work.Spaces.eta)]
  have h3 : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show f θ ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
        = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) (Work.Spaces.eta)]
  have hsub : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (1 / (1 + Work.Spaces.eta) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + C0 * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    have h := hC0 f hf hf0 hfpi
    rw [h1, h2, h3,
      show (1 : ℝ) / (Work.Spaces.eta + 1) ^ 2 = 1 / (1 + Work.Spaces.eta) ^ 2 by ring] at h
    exact h
  calc (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := hstep1
    _ ≤ (1 / (1 + Work.Spaces.eta) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + C0 * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := hsub

end Work.FTS.EllipticEst.AngSecond
