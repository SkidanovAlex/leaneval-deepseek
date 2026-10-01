/-
# `F(-λ) = 8/5` for the test function of HB (1992), Lemma 7.2

The Laplace transform `F z = ∫₀^{2/λ} e^{-zt} f(t) dt` of the test function `f = g ∗ g`
at `z = -λ` is the real integral `∫₀^{2/λ} e^{λt} f(t) dt` (with `f` the explicit cubic-times-quadratic
polynomial of `testFn72_defs`), whose value is `8/5`.

The evaluation is by an explicit antiderivative: with

  `q(t) = -8/5 + (8λ/3) t - (4λ²/3) t² + (λ⁴/6) t⁴ - (λ⁵/30) t⁵`

one has `(e^{λt} q(t))' = e^{λt} (λ q(t) + q'(t))` and the polynomial identity

  `λ q(t) + q'(t) = (λ/30)(2 - λt)³ (4 + 6λt + λ²t²)`,

so that on `[0, 2/λ]` the derivative of `e^{λt} q(t)` is exactly `e^{λt} f(t)`.  Since
`q(2/λ) = 0` and `q(0) = -8/5`, the fundamental theorem of calculus gives `8/5`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

noncomputable section
namespace Work.ZeroFreeTables

/-- The antiderivative polynomial `q` for `e^{λt} f(t)`, normalised so that `q(0) = -8/5`
and `q(2/λ) = 0`. -/
def tf72Q (lam t : ℝ) : ℝ :=
  -8/5 + (8*lam/3)*t - (4*lam^2/3)*t^2 + (lam^4/6)*t^4 - (lam^5/30)*t^5

lemma hasDerivAt_tf72Q (lam t : ℝ) :
    HasDerivAt (tf72Q lam)
      (8*lam/3 - (8*lam^2/3)*t + (2*lam^4/3)*t^3 - (lam^5/6)*t^4) t := by
  have h0 : HasDerivAt (fun _ : ℝ => (-8/5 : ℝ)) 0 t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun s : ℝ => (8*lam/3)*s) (8*lam/3) t := by
    simpa using (hasDerivAt_id t).const_mul (8*lam/3)
  have h2 : HasDerivAt (fun s : ℝ => (4*lam^2/3)*s^2) ((4*lam^2/3)*(2*t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_mul (4*lam^2/3))
  have h4 : HasDerivAt (fun s : ℝ => (lam^4/6)*s^4) ((lam^4/6)*(4*t^3)) t := by
    simpa using ((hasDerivAt_pow 4 t).const_mul (lam^4/6))
  have h5 : HasDerivAt (fun s : ℝ => (lam^5/30)*s^5) ((lam^5/30)*(5*t^4)) t := by
    simpa using ((hasDerivAt_pow 5 t).const_mul (lam^5/30))
  have h := (((h0.add h1).sub h2).add h4).sub h5
  have hfun : tf72Q lam
      = fun s : ℝ => ((-8/5 : ℝ) + (8*lam/3)*s - (4*lam^2/3)*s^2
          + (lam^4/6)*s^4 - (lam^5/30)*s^5) := by
    funext s; unfold tf72Q; ring
  rw [hfun]
  exact h.congr_deriv (by ring)

/-- `(e^{λt} q(t))' = e^{λt} (λ/30)(2-λt)³(4+6λt+λ²t²)`, the polynomial body of the
integrand of `tf72Fc lam (-lam)`. -/
lemma hasDerivAt_exp_tf72Q (lam t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (lam*s) * tf72Q lam s)
      (Real.exp (lam*t) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (lam*s)) (Real.exp (lam*t)*lam) t := by
    have h : HasDerivAt (fun s : ℝ => lam * s) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    simpa using h.exp
  have hm := hexp.mul (hasDerivAt_tf72Q lam t)
  refine hm.congr_deriv ?_
  unfold tf72Q
  ring

/-- The Laplace-type integral of the test function at `-λ`: `∫₀^{2/λ} e^{λt} f(t) dt = 8/5`. -/
lemma integral_exp_tf72f (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in (0:ℝ)..(2/lam), Real.exp (lam*t) * tf72f lam t = 8/5 := by
  have h2pos : (0:ℝ) < 2/lam := by positivity
  have hcont : ContinuousOn (fun s : ℝ => Real.exp (lam*s) * tf72Q lam s)
      (Set.Icc (0:ℝ) (2/lam)) :=
    (Continuous.continuousOn (by unfold tf72Q; fun_prop))
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (2/lam),
      HasDerivAt (fun s : ℝ => Real.exp (lam*s) * tf72Q lam s)
        (Real.exp (lam*x) * tf72f lam x) x := by
    intro x hx
    rw [tf72f_eq_poly lam hlam x (Set.Ioo_subset_Icc_self hx)]
    exact hasDerivAt_exp_tf72Q lam x
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (lam*t) * tf72f lam t)
      MeasureTheory.volume (0:ℝ) (2/lam) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
    exact (tf72f_cont lam hlam).mono (by
      intro x hx
      rw [Set.uIcc_of_le h2pos.le] at hx
      exact hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h2pos.le hcont hderiv hint]
  have hq0 : tf72Q lam 0 = -8/5 := by unfold tf72Q; norm_num
  have hq2 : tf72Q lam (2/lam) = 0 := by unfold tf72Q; field_simp; ring
  have harg : lam * (2/lam) = 2 := by field_simp
  rw [hq2, hq0, harg]
  norm_num

theorem tf72Fc_neglam_re (lam : ℝ) (hlam : 0 < lam) :
    (Work.ZeroFreeTables.tf72Fc lam ((-(lam) : ℝ) : ℂ)).re = 8 / 5 := by
  have hmain : tf72Fc lam ((-(lam) : ℝ) : ℂ)
      = (((∫ t in (0:ℝ)..(2/lam), Real.exp (lam*t) * tf72f lam t) : ℝ) : ℂ) := by
    unfold tf72Fc
    have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) (2/lam),
        Complex.exp (-((↑(-lam) : ℂ) * (t:ℂ))) * ((tf72f lam t : ℝ):ℂ)
          = ((Real.exp (lam*t) * tf72f lam t : ℝ) : ℂ) := by
      intro t _
      have hz : -((↑(-lam) : ℂ) * (t:ℂ)) = ((lam*t : ℝ) : ℂ) := by push_cast; ring
      rw [hz, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
  rw [hmain, integral_exp_tf72f lam hlam]
  norm_num

end Work.ZeroFreeTables
