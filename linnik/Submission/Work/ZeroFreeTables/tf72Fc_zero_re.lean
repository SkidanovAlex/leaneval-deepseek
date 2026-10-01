import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

/-!
# `tf72Fc_zero_re` — the value `F(0) = 8/9` of HB's test-function transform

Heath-Brown (1992), Lemma 7.2: for the test function `f = g ∗ g` of
`testFn72_defs`, the Laplace transform `F z = ∫₀^{2/λ} e^{−zt} f t dt` takes the
value `F 0 = ∫₀^{2/λ} f t dt = 8/9` at the origin.

We prove the underlying real integral once (`tf72f_intervalIntegral`), via the
substitution `u = λ t` and the rational integral `tf72_poly_integral`, and then
transfer it to the complex-valued transform `tf72Fc` using
`intervalIntegral.integral_ofReal`.
-/

noncomputable section
namespace Work.ZeroFreeTables

/-- The elementary integral `∫₀² (2−u)³(4+6u+u²) du = 80/3`, obtained from the
explicit expansion `(2−u)³(4+6u+u²) = 32 − 40u² + 20u³ − u⁵`. -/
theorem tf72_poly_integral : (∫ u in (0:ℝ)..2, (2-u)^3*(4+6*u+u^2)) = 80/3 := by
  have hpt : Set.EqOn (fun u : ℝ => (2-u)^3*(4+6*u+u^2))
      (fun u : ℝ => 32 - 40*u^2 + 20*u^3 - u^5) (Set.uIcc 0 2) :=
    fun u _ => by ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => 32*x - (40/3)*x^3 + 5*x^4 - x^6/6)
        (f' := fun x : ℝ => 32 - 40*x^2 + 20*x^3 - x^5)]
  · norm_num
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => 32*y) (32:ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (32:ℝ)
    have h2 : HasDerivAt (fun y : ℝ => (40/3)*y^3) ((40/3)*(3*x^2)) x := by
      simpa using (hasDerivAt_pow 3 x).const_mul (40/3)
    have h3 : HasDerivAt (fun y : ℝ => 5*y^4) (5*(4*x^3)) x := by
      simpa using (hasDerivAt_pow 4 x).const_mul (5:ℝ)
    have h4 : HasDerivAt (fun y : ℝ => y^6/6) ((6*x^5)/6) x := by
      simpa using (hasDerivAt_pow 6 x).div_const (6:ℝ)
    have hmain : HasDerivAt (fun y : ℝ => 32*y - (40/3)*y^3 + 5*y^4 - y^6/6)
        (32 - (40/3)*(3*x^2) + 5*(4*x^3) - (6*x^5)/6) x :=
      ((h1.sub h2).add h3).sub h4
    exact hmain.congr_deriv (by ring)
  · exact (by fun_prop : Continuous fun x : ℝ => 32 - 40*x^2 + 20*x^3 - x^5)
      |>.intervalIntegrable 0 2

/-- `∫₀^{2/λ} f t dt = 8/9` for HB's test function `f` (Lemma 7.2 at `x = 0`). -/
theorem tf72f_intervalIntegral (lam : ℝ) (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..(2/lam), tf72f lam t) = 8 / 9 := by
  have hpoly : (∫ t in (0:ℝ)..(2/lam), tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam), (lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hle : (0:ℝ) ≤ 2/lam := by positivity
    rw [Set.uIcc_of_le hle] at ht
    exact tf72f_eq_poly lam hlam t ht
  rw [hpoly]
  have hpt : Set.EqOn (fun t : ℝ => (lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2))
      (fun t : ℝ => (lam/30) * ((2-(lam*t))^3*(4+6*(lam*t)+(lam*t)^2)))
      (Set.uIcc 0 (2/lam)) :=
    fun t _ => by ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => (lam/30) * ((2-u)^3*(4+6*u+u^2))) hlam.ne']
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, tf72_poly_integral]
  have hne : lam ≠ 0 := hlam.ne'
  field_simp
  ring

/-- `tf72Fc lam z = ∫₀^{2/λ} e^{−zt} f t dt` at `z = 0` is the real integral of `f`. -/
theorem tf72Fc_zero (lam : ℝ) :
    tf72Fc lam 0 = ((∫ t in (0:ℝ)..(2/lam), tf72f lam t : ℝ) : ℂ) := by
  have hintegrand : (∫ t in (0:ℝ)..(2/lam),
        Complex.exp (-((0:ℂ) * (t:ℂ))) * ((tf72f lam t : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..(2/lam), ((tf72f lam t : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun t _ => by simp
  rw [tf72Fc, hintegrand, intervalIntegral.integral_ofReal]

theorem tf72Fc_zero_re (lam : ℝ) (hlam : 0 < lam) :
    (Work.ZeroFreeTables.tf72Fc lam 0).re = 8 / 9 := by
  rw [tf72Fc_zero lam, Complex.ofReal_re, tf72f_intervalIntegral lam hlam]

end Work.ZeroFreeTables
