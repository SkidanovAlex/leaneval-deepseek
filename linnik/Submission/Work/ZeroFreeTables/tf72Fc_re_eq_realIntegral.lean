import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

/-!
# The real part of the complex Laplace transform `tf72Fc`

`tf72Fc lam z = ∫₀^{2/λ} e^{-zt} f(t) dt` is defined for complex `z` (the definition
`tf72Fc` integrates the complex-valued integrand `e^{-zt} * (f t : ℂ)`).  For real `z`
its real part is the ordinary real Laplace integral `∫₀^{2/λ} e^{-zt} f(t) dt`: the
complex integrand is pointwise the cast of the real one, and the interval integral of a
real-valued function cast to `ℂ` is the cast of the real interval integral
(`intervalIntegral.integral_ofReal`).  No integrability hypothesis (nor a sign condition
on `λ`) is needed, because both statements are identities between integrals of *equal*
integrands; in particular they hold also in the degenerate/junk cases.
-/

namespace Work.ZeroFreeTables

theorem tf72Fc_re_eq_realIntegral (lam z : ℝ) :
    (Work.ZeroFreeTables.tf72Fc lam (z : ℂ)).re
      = ∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * Work.ZeroFreeTables.tf72f lam t := by
  -- The complex integrand of `tf72Fc` is pointwise the cast of the real integrand.
  have hpt : ∀ t : ℝ,
      Complex.exp (-((z : ℂ) * (t : ℂ))) * ((tf72f lam t : ℝ) : ℂ)
        = ((Real.exp (-(z * t)) * tf72f lam t : ℝ) : ℂ) := by
    intro t
    have h1 : -((z : ℂ) * (t : ℂ)) = ((-(z * t) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have hmain : (∫ t in (0:ℝ)..(2/lam),
        Complex.exp (-((z : ℂ) * (t : ℂ))) * ((tf72f lam t : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..(2/lam), ((Real.exp (-(z * t)) * tf72f lam t : ℝ) : ℂ) :=
    intervalIntegral.integral_congr (fun t _ => hpt t)
  unfold tf72Fc
  rw [hmain, intervalIntegral.integral_ofReal, Complex.ofReal_re]

end Work.ZeroFreeTables
