import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- If `g` is `C²` on `ℝ` and has vanishing second derivative everywhere, then `g` is affine.

The proof is the two FTC steps `0 = ∫₀ᵗ g'' = g'(t) - g'(0)` (so `g'` is constant) and
`g(t) - g(0) = ∫₀ᵗ g' = t · g'(0)`. -/
lemma affine_of_deriv_deriv_eq_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (h : ∀ t, deriv (deriv g) t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, g t = c1 + c2 * t := by
  have hdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hg' : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hcont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  -- First step: `deriv g` is constant, because `deriv (deriv g) ≡ 0`.
  have hstep1 : ∀ s, deriv g s = deriv g 0 := by
    intro s
    have hh : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (deriv g) (deriv (deriv g) x) x :=
      fun x _ => (hdg x).hasDerivAt
    have hint : IntervalIntegrable (deriv (deriv g)) MeasureTheory.volume 0 s := by
      have hz : deriv (deriv g) = fun _ => (0 : ℝ) := funext h
      rw [hz]
      exact intervalIntegrable_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hh hint
    have hzero : (∫ x in (0 : ℝ)..s, deriv (deriv g) x) = 0 := by
      simp [h]
    linarith [hftc, hzero]
  refine ⟨g 0, deriv g 0, fun t => ?_⟩
  -- Second step: `g t - g 0 = ∫₀ᵗ g' = t · g'(0)`.
  have hstep2 : (∫ x in (0 : ℝ)..t, deriv g x) = g t - g 0 := by
    have hh : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt g (deriv g x) x :=
      fun x _ => (hg' x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hh (hcont.intervalIntegrable 0 t)
  have hInt : (∫ x in (0 : ℝ)..t, deriv g x) = t * deriv g 0 := by
    calc (∫ x in (0 : ℝ)..t, deriv g x) = ∫ x in (0 : ℝ)..t, deriv g 0 := by
          apply intervalIntegral.integral_congr
          intro x _
          exact hstep1 x
      _ = t * deriv g 0 := by
          rw [intervalIntegral.integral_const]
          simp
  have h3 : g t = g 0 + t * deriv g 0 := by linarith [hstep2, hInt]
  rw [h3]
  ring

theorem ode_rep_double {a b r : ℝ} (ha : a = -2 * r) (hb : b = r ^ 2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, U t = (c1 + c2 * t) * Real.exp (r * t) := by
  -- The substitution `W t = U t · e^{-rt}` turns the double-root equation
  -- `U'' - 2r U' + r² U = 0` into `W'' = 0`.
  have hdU : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdU' : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have hW : ContDiff ℝ 2 (fun t => U t * Real.exp (-(r * t))) := by fun_prop
  -- Explicit first derivative of `W`.
  have hderivW : deriv (fun t => U t * Real.exp (-(r * t)))
      = fun t => (deriv U t - r * U t) * Real.exp (-(r * t)) := by
    funext t
    show deriv (U * fun s => Real.exp (-(r * s))) t
        = (deriv U t - r * U t) * Real.exp (-(r * t))
    rw [deriv_mul (hdU t) (by fun_prop)]
    rw [deriv_exp (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => -(r * t)) t)]
    simp
    ring
  -- `W'' = e^{-rt} (U'' + a U' + b U) = 0`.
  have hW2 : ∀ t, deriv (deriv (fun t => U t * Real.exp (-(r * t)))) t = 0 := by
    intro t
    rw [hderivW]
    have hV : deriv (fun s => (deriv U s - r * U s) * Real.exp (-(r * s))) t
        = Real.exp (-(r * t))
          * (deriv (deriv U) t + (-2 * r) * deriv U t + r ^ 2 * U t) := by
      show deriv ((fun s => deriv U s - r * U s) * fun s => Real.exp (-(r * s))) t = _
      rw [deriv_mul (by fun_prop) (by fun_prop)]
      have hA : deriv (fun s => deriv U s - r * U s) t
          = deriv (deriv U) t - r * deriv U t := by
        show deriv ((deriv U) - fun s => r * U s) t = _
        rw [deriv_sub (hdU' t) (by fun_prop : DifferentiableAt ℝ (fun s => r * U s) t)]
        rw [deriv_const_mul r (hdU t)]
      rw [hA, deriv_exp (by fun_prop)]
      simp
      ring
    rw [hV]
    have hode' : deriv (deriv U) t + (-2 * r) * deriv U t + r ^ 2 * U t = 0 := by
      have ht := hode t
      rw [ha, hb] at ht
      exact ht
    rw [hode']
    ring
  obtain ⟨c1, c2, hc⟩ := affine_of_deriv_deriv_eq_zero hW hW2
  refine ⟨c1, c2, fun t => ?_⟩
  have hexp : Real.exp (-(r * t)) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add]
    have : -(r * t) + r * t = 0 := by ring
    rw [this, Real.exp_zero]
  have h2 : (c1 + c2 * t) * Real.exp (r * t) = U t := by
    rw [(hc t).symm, mul_assoc, hexp, mul_one]
  exact h2.symm

end Work.FTS.StrongEps.EComparison
