import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.I4BV.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.I4BV.tail_setIntegral_tendsto_zero
import Submission.Work.FTS.EllipticEst.I4BV.exists_tendsto_nhdsLT_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.I4BV.i4_rate_alt
import Submission.Work.FTS.EllipticEst.I4BV.i4_limit_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

/-- **The vanishing of the `I₄` boundary term.**

Let `ψ` be a function of the angular variable, of class `C²` on the open interval `(0, π/2)`,
whose weighted square `∫_θ ψ² (sin 2θ)^{-η}` is finite (`η = 99/100`), and for which
`P := fun θ => cos²θ · ψ'(θ)` satisfies `∫_θ (P'(θ)/cos θ)² (sin 2θ)^{-η} < ∞`.
Then the boundary quantity `(sin θ / cos³θ) · P(θ)² · (sin 2θ)^{-η}` tends to `0` as
`θ → π/2⁻`.

Proof route: (1) `∫ (P'/c)²σ < ∞` and `∫_θ^{π/2} c²σ^{-1} ≤ C(π/2-θ)^{3+η}` (from the
elementary pointwise bound `cos²θ·(sin 2θ)^η ≤ 2^η(π/2-θ)^{2+η}`) give `P' ∈ L¹`, hence by
the Cauchy criterion `|P(θ)-P(θ')| ≤ (∫_θ^{θ'}(P'/c)²σ)^{1/2}(∫_θ^{θ'}c²σ^{-1})^{1/2}
≤ C(π/2-θ)^{(3+η)/2}√(V θ)` with `V θ = ∫_θ^{π/2}(P'/c)²σ`, that `L := lim_{θ→π/2}P(θ)`
exists and `|P(θ)-L| ≤ C(π/2-θ)^{(3+η)/2}√(V θ)`; (2) `L = 0`, since `L ≠ 0` forces
`|ψ'| ≥ (|L|/2)cos^{-2}θ ≥ (|L|/2)(π/2-θ)^{-2}` and hence `|ψ| ≥ (|L|/4)(π/2-θ)^{-1}` near
`π/2`, so `∫ψ²σ ≥ (|L|²/16)∫(π/2-θ)^{-2}dθ = ∞` because `σ = (sin 2θ)^{-η} ≥ 1`, contradicting
the hypothesis; (3) `V θ → 0`, so `P(θ)²(π/2-θ)^{-3-η} ≤ C²·V θ → 0`, and
`(sin θ/cos³θ)·σ ≤ C(π/2-θ)^{-3-η}` (`sin θ ≤ 1`, `cos θ ≥ (2/π)(π/2-θ)`,
`sin(2θ) ≥ (4/π)(π/2-θ)`) finishes the proof. -/
theorem I4BoundaryVanish (ψ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hquarter : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hhalf : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  have hneghalf : -(Real.pi / 2) < (0 : ℝ) := by linarith [Real.pi_pos]
  have hPderiv : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ')
        (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 ψ x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv ψ) x := h2.derivWithin (by norm_num)
    have hdψ : DifferentiableAt ℝ (deriv ψ) x := hd1.differentiableAt (by norm_num)
    have hP : DifferentiableAt ℝ (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x := by
      fun_prop
    exact hP.hasDerivAt
  obtain ⟨L, hLtend, hLrate⟩ :=
    I4BV.i4_rate_alt (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') hPderiv hB
  have hL0 : L = 0 := I4BV.i4_limit_eq_zero ψ L hsm hA hLtend
  have hVtend : Filter.Tendsto
      (fun t => ∫ x in Set.Ioo t (Real.pi / 2),
        (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
          * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    I4BV.tail_setIntegral_tendsto_zero (a := 0) (b := Real.pi / 2) hpi2 hB
  have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := Real.pi / 4) hquarter]
    exact self_mem_nhdsWithin
  have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 * I4BV.s4 θ
      ≤ (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
    intro θ hθ
    have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_trans hpi4 hθ.1, hθ.2⟩
    have hu : 0 < Real.pi / 2 - θ := sub_pos.mpr hθ.2
    have h1 := I4BV.coef_le hθ
    have h2 := hLrate θ hI
    rw [hL0] at h2
    calc Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 * I4BV.s4 θ
        = (Real.sin θ / (Real.cos θ) ^ 3 * I4BV.s4 θ)
          * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 := by ring
      _ ≤ (I4BV.K4 * (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ)))
          * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
            * ∫ x in Set.Ioo θ (Real.pi / 2),
                (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                  * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ))) := by
          apply mul_le_mul h1 ?_ (sq_nonneg _) ?_
          · simpa using h2
          · rw [I4BV.K4]; positivity
      _ = I4BV.K4 * 2 ^ (99 / 100 : ℝ)
          * ((Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ))
            * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ))
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by ring
      _ = (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
          have hc : (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ))
              * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) = 1 := by
            rw [← Real.rpow_add hu,
              show -(3 + 99 / 100 : ℝ) + (3 + 99 / 100 : ℝ) = 0 by ring, Real.rpow_zero]
          rw [hc]; ring
  change Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
        * I4BV.s4 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
  have hbound : Filter.Tendsto
      (fun t => (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo t (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hVtend.const_mul (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
  refine squeeze_zero_norm' (a := fun t => (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo t (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
    ?_ hbound
  filter_upwards [hmem] with θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_trans hpi4 hθ.1, hθ.2⟩
  have hsinnn : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hI.1 (lt_trans hI.2 hhalf))
  have hcosnn : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨lt_trans hneghalf hI.1, hI.2⟩)
  have hs4nn : 0 ≤ I4BV.s4 θ := by
    rw [I4BV.s4]
    exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hI.1])
      (by linarith [hI.2, Real.pi_pos]))) _
  have hnn : 0 ≤ Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
      * I4BV.s4 θ :=
    mul_nonneg (mul_nonneg (div_nonneg hsinnn (by positivity)) (sq_nonneg _)) hs4nn
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hkey θ hθ

end Work.FTS.EllipticEst.Honest
