import Mathlib
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

/-- The real part of the complex integrand of the Laplace transform is the real
integrand: `Re (e^{-xt} f(t)) = e^{-xt} f(t)`. -/
lemma TestFn_F_eq_integral_aux_point (T : TestFn) (x t : ℝ) :
    (Complex.exp (-((x : ℂ) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re
      = Real.exp (-(x * t)) * T.f t := by
  have hexp : Complex.exp (-((x : ℂ) * (t : ℂ))) = ((Real.exp (-(x * t)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hexp, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The complex integrand of the Laplace transform is interval integrable. -/
lemma TestFn_F_eq_integral_aux_int (T : TestFn) (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))) * ((T.f t : ℝ) : ℂ))
      MeasureTheory.volume (0 : ℝ) T.x₀ := by
  have hlin : Continuous (fun t : ℝ => -((x : ℂ) * (t : ℂ))) := by fun_prop
  have hf : ContinuousOn (fun t : ℝ => ((T.f t : ℝ) : ℂ)) (Set.Icc (0 : ℝ) T.x₀) :=
    Complex.continuous_ofReal.comp_continuousOn
      (T.f_cont.mono (fun t ht => ht.1))
  exact ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos)
    ((Complex.continuous_exp.comp hlin).continuousOn.mul hf)

theorem TestFn_F_eq_integral (T : TestFn) (x : ℝ) :
    T.F x = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(x * t)) * T.f t := by
  have hstep : (∫ t in (0:ℝ)..T.x₀,
        Complex.exp (-((x : ℂ) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(x * t)) * T.f t := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
      (TestFn_F_eq_integral_aux_int T x)]
    exact intervalIntegral.integral_congr
      (fun t _ => by rw [Complex.reCLM_apply, TestFn_F_eq_integral_aux_point T x t])
  calc T.F x = (T.Fc (x : ℂ)).re := rfl
    _ = (∫ t in (0:ℝ)..T.x₀,
          Complex.exp (-((x : ℂ) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
          rw [T.Fc_spec]
    _ = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(x * t)) * T.f t := hstep

end Work.ZeroFreeTables
