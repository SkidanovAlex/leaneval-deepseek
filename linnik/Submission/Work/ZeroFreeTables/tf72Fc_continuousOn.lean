import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

namespace Work.ZeroFreeTables

open MeasureTheory intervalIntegral

/-- The polynomial that agrees with `tf72f lam` on `[0, 2/lam]` (HB Lemma 7.2). -/
private noncomputable def tf72poly (lam : ℝ) (t : ℝ) : ℝ :=
  (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)

private lemma tf72poly_cont (lam : ℝ) :
    Continuous (tf72poly lam) := by
  unfold tf72poly; fun_prop

/-- On `[0, 2/lam]`, the test function `tf72f lam` coincides with the continuous
polynomial `tf72poly lam`. -/
private lemma tf72f_eq_tf72poly (lam : ℝ) (hlam : 0 < lam) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (2/lam)) : tf72f lam t = tf72poly lam t := by
  unfold tf72poly
  exact tf72f_eq_poly lam hlam t ht

/-- The complex Laplace transform `tf72Fc lam` is continuous everywhere: on the
interval of integration it equals the (everywhere continuous) integrand built
from the polynomial `tf72poly`, and the corresponding parametric integral is
continuous by the standard continuity theorem for parametric interval integrals. -/
theorem tf72Fc_continuous (lam : ℝ) (hlam : 0 < lam) :
    Continuous (Work.ZeroFreeTables.tf72Fc lam) := by
  have hcont : Continuous (fun z : ℂ => ∫ t in (0:ℝ)..(2/lam),
      Complex.exp (-(z * (t:ℂ))) * (((tf72poly lam t : ℝ)) : ℂ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    · show Continuous (Function.uncurry (fun (z : ℂ) (t : ℝ) =>
        Complex.exp (-(z * (t:ℂ))) * (((tf72poly lam t : ℝ)) : ℂ)))
      have := tf72poly_cont lam
      fun_prop
  refine hcont.congr ?_
  intro z
  unfold tf72Fc
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 2/lam)] at ht
  simp only [tf72f_eq_tf72poly lam hlam t ht]

theorem tf72Fc_continuousOn (lam : ℝ) (hlam : 0 < lam) :
    ContinuousOn (Work.ZeroFreeTables.tf72Fc lam) {z : ℂ | 0 ≤ z.re} :=
  (tf72Fc_continuous lam hlam).continuousOn

end Work.ZeroFreeTables
