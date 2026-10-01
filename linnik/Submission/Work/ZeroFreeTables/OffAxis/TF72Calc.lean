/-
# OffAxis/TF72Calc

The three scale-invariance identities for the Lemma 7.2 test function
`f = tf72f` of Heath-Brown (1992) (see
`Submission/Work/ZeroFreeTables/testFn72_defs.lean`):

* `∫₀^{2/λ} x f_λ(x) dx = 16/(35λ)`,
* `∫₀^{2/λ} x e^{λx} f_λ(x) dx = 16/(15λ)`,
* `Re F_λ(z) = Re F_1(z/λ)` for every `z : ℂ`, where `F_λ` is the complex Laplace
  transform `tf72Fc λ`.

All three follow from the scaling identity `f_λ(x) = λ · f_1(λx)` (`tf72f_scale`)
together with two computations at the self-similar scale `λ = 1`:

* `∫₀² u f_1(u) du = 16/35` (`tf72f_moment_one`), a polynomial integral;
* `∫₀² u e^u f_1(u) du = 16/15` (`tf72f_expmoment_one`), whose anti-derivative is
  `e^u S(u)` with `S(u) = P - P' + P'' - ... = (1/5)u⁵ - (1/3)u⁴ - (1/30)u⁶ + (16/15)u - 16/15`
  for `P(u) = (16/15)u - (4/3)u³ + (2/3)u⁴ - (1/30)u⁶`, so that `S + S' = P`,
  `S(2) = 0` and `S(0) = -16/15`.

The complex identity is the same substitution `t = u/λ` in the Bochner integral
(`intervalIntegral.integral_comp_mul_left`), the factor `λ` coming from
`tf72f_scale` cancelling the Jacobian `1/λ`; note that the two sides are in fact
*equal* as complex numbers, so taking real parts is immediate.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

open MeasureTheory
open scoped Interval

namespace Work.ZeroFreeTables

/-- Scaling of the Lemma 7.2 test function: `f_λ(x) = λ · f_1(λx)` for `λ > 0`. -/
theorem tf72f_scale (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    tf72f lam x = lam * tf72f 1 (lam * x) := by
  unfold tf72f
  rcases le_or_gt 0 x with hx | hx
  · rw [if_pos hx, if_pos (mul_nonneg hlam.le hx)]
    simp only [one_mul, one_pow]
    ring
  · rw [if_neg (not_le.mpr hx), if_neg (not_le.mpr (mul_neg_of_pos_of_neg hlam hx)), mul_zero]

/-- First moment of the test function at the self-similar scale `λ = 1`:
`∫₀² u · f_1(u) du = 16/35`.  On `[0,2]` the integrand is the sextic
`(16/15)u - (4/3)u³ + (2/3)u⁴ - (1/30)u⁶` with primitive
`(8/15)u² - (1/3)u⁴ + (2/15)u⁵ - (1/210)u⁷`. -/
theorem tf72f_moment_one :
    (∫ u in (0:ℝ)..2, u * tf72f 1 u) = 16/35 := by
  have hpt : ∀ u ∈ Set.uIcc (0:ℝ) 2, u * tf72f 1 u
      = (16/15)*u - (4/3)*u^3 + (2/3)*u^4 - (1/30)*u^6 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hu
    rw [tf72f_eq_poly 1 (by norm_num) u (by simpa using hu)]
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => (8/15)*x^2 - (1/3)*x^4 + (2/15)*x^5 - (1/210)*x^7)
      (f' := fun x : ℝ => (16/15)*x - (4/3)*x^3 + (2/3)*x^4 - (1/30)*x^6)]
  · norm_num
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => (8/15)*y^2) ((8/15)*(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul ((8:ℝ)/15)
    have h2 : HasDerivAt (fun y : ℝ => (1/3)*y^4) ((1/3)*(4*x^3)) x := by
      simpa using (hasDerivAt_pow 4 x).const_mul ((1:ℝ)/3)
    have h3 : HasDerivAt (fun y : ℝ => (2/15)*y^5) ((2/15)*(5*x^4)) x := by
      simpa using (hasDerivAt_pow 5 x).const_mul ((2:ℝ)/15)
    have h4 : HasDerivAt (fun y : ℝ => (1/210)*y^7) ((1/210)*(7*x^6)) x := by
      simpa using (hasDerivAt_pow 7 x).const_mul ((1:ℝ)/210)
    have hmain : HasDerivAt
        (fun y : ℝ => (8/15)*y^2 - (1/3)*y^4 + (2/15)*y^5 - (1/210)*y^7)
        ((8/15)*(2*x) - (1/3)*(4*x^3) + (2/15)*(5*x^4) - (1/210)*(7*x^6)) x :=
      ((h1.sub h2).add h3).sub h4
    exact hmain.congr_deriv (by ring)
  · exact (by fun_prop : Continuous fun x : ℝ =>
        (16/15)*x - (4/3)*x^3 + (2/3)*x^4 - (1/30)*x^6).intervalIntegrable 0 2

/-- Exponential first moment of the test function at the self-similar scale
`λ = 1`: `∫₀² u · e^u · f_1(u) du = 16/15`.  With `P(u) = u f_1(u)` the sextic
above, the primitive is `e^u S(u)` where
`S(u) = (1/5)u⁵ - (1/3)u⁴ - (1/30)u⁶ + (16/15)u - 16/15`, and `S(2) = 0`,
`S(0) = -16/15`. -/
theorem tf72f_expmoment_one :
    (∫ u in (0:ℝ)..2, u * Real.exp u * tf72f 1 u) = 16/15 := by
  have hpt : ∀ u ∈ Set.uIcc (0:ℝ) 2, u * Real.exp u * tf72f 1 u
      = Real.exp u * ((16/15)*u - (4/3)*u^3 + (2/3)*u^4 - (1/30)*u^6) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hu
    rw [tf72f_eq_poly 1 (by norm_num) u (by simpa using hu)]
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ =>
        Real.exp x * ((1/5)*x^5 - (1/3)*x^4 - (1/30)*x^6 + (16/15)*x - 16/15))
      (f' := fun x : ℝ =>
        Real.exp x * ((16/15)*x - (4/3)*x^3 + (2/3)*x^4 - (1/30)*x^6))]
  · simp only [Real.exp_zero, mul_zero, one_mul] <;> norm_num
  · intro x _
    have h5 : HasDerivAt (fun y : ℝ => (1/5)*y^5) ((1/5)*(5*x^4)) x := by
      simpa using (hasDerivAt_pow 5 x).const_mul ((1:ℝ)/5)
    have h4 : HasDerivAt (fun y : ℝ => (1/3)*y^4) ((1/3)*(4*x^3)) x := by
      simpa using (hasDerivAt_pow 4 x).const_mul ((1:ℝ)/3)
    have h6 : HasDerivAt (fun y : ℝ => (1/30)*y^6) ((1/30)*(6*x^5)) x := by
      simpa using (hasDerivAt_pow 6 x).const_mul ((1:ℝ)/30)
    have h1 : HasDerivAt (fun y : ℝ => (16/15)*y) ((16/15)*1) x := by
      simpa using (hasDerivAt_id x).const_mul ((16:ℝ)/15)
    have h0 : HasDerivAt (fun _ : ℝ => (16/15:ℝ)) 0 x := hasDerivAt_const x (16/15)
    have hS : HasDerivAt
        (fun y : ℝ => (1/5)*y^5 - (1/3)*y^4 - (1/30)*y^6 + (16/15)*y - 16/15)
        (x^4 - (4/3)*x^3 - (1/5)*x^5 + 16/15) x :=
      (((h5.sub h4).sub h6).add h1).sub h0 |>.congr_deriv (by ring)
    have hS2 : HasDerivAt
        (fun y : ℝ =>
          Real.exp y * ((1/5)*y^5 - (1/3)*y^4 - (1/30)*y^6 + (16/15)*y - 16/15))
        (Real.exp x * ((1/5)*x^5 - (1/3)*x^4 - (1/30)*x^6 + (16/15)*x - 16/15)
          + Real.exp x * (x^4 - (4/3)*x^3 - (1/5)*x^5 + 16/15)) x :=
      (Real.hasDerivAt_exp x).mul hS
    exact hS2.congr_deriv (by ring)
  · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.exp x * ((16/15)*x - (4/3)*x^3 + (2/3)*x^4 - (1/30)*x^6))
      |>.intervalIntegrable 0 2

/-- The complex Laplace transform of the test function is invariant under the
scaling `λ ↦ 1` with the argument divided by `λ`: `F_λ(z) = F_1(z/λ)` (as complex
numbers, for every `z : ℂ`, when `λ > 0`). -/
theorem tf72Fc_scale (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    tf72Fc lam z = tf72Fc 1 (z / (lam : ℂ)) := by
  have hsub : (∫ t in (0:ℝ)..(2/lam),
        Complex.exp (-(z * (t:ℂ))) * ((tf72f lam t : ℝ):ℂ))
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => (lam:ℂ) * (Complex.exp (-((z/(lam:ℂ)) * ((u:ℝ):ℂ)))
            * ((tf72f 1 u : ℝ):ℂ))) (lam * t) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show Complex.exp (-(z * (t:ℂ))) * ((tf72f lam t : ℝ):ℂ)
      = (lam:ℂ) * (Complex.exp (-((z/(lam:ℂ)) * (((lam*t:ℝ)):ℂ)))
          * ((tf72f 1 (lam*t) : ℝ):ℂ))
    have h1 : ((tf72f lam t : ℝ):ℂ) = (lam:ℂ) * ((tf72f 1 (lam*t) : ℝ):ℂ) := by
      rw [tf72f_scale lam hlam t, Complex.ofReal_mul]
    have h2 : (z/(lam:ℂ)) * (((lam*t:ℝ)):ℂ) = z * (t:ℂ) := by
      have hL : ((lam:ℝ):ℂ) ≠ 0 := by
        intro hh
        exact hlam.ne' ((Complex.ofReal_eq_zero).mp hh)
      rw [show (((lam*t:ℝ)):ℂ) = (lam:ℂ) * (t:ℂ) by push_cast; ring]
      rw [div_eq_mul_inv, mul_assoc, ← mul_assoc ((lam:ℂ))⁻¹ ((lam:ℂ)) (t:ℂ),
          inv_mul_cancel₀ hL, one_mul]
    have h2neg : -((z/(lam:ℂ)) * (((lam*t:ℝ)):ℂ)) = -(z * (t:ℂ)) := by rw [h2]
    rw [h1, h2neg]
    ring
  unfold tf72Fc
  rw [show (2:ℝ)/1 = 2 by norm_num]
  rw [hsub]
  rw [intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => (lam:ℂ) * (Complex.exp (-((z/(lam:ℂ)) * ((u:ℝ):ℂ)))
          * ((tf72f 1 u : ℝ):ℂ))) hlam.ne']
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp]
  rw [intervalIntegral.integral_const_mul]
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam.ne',
      Complex.ofReal_one, one_mul]

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables.OffAxis

/-- **HB Lemma 7.2, computation block**: the two first-moment integrals of the
test function `tf72f λ` and the scaling identity for its complex Laplace
transform. -/
theorem TF72Calc (lam : ℝ) (hlam : 0 < lam) :
    (∫ x in (0:ℝ)..(2/lam), x * Work.ZeroFreeTables.tf72f lam x) = 16/(35*lam)
    ∧ (∫ x in (0:ℝ)..(2/lam), x * Real.exp (lam*x) * Work.ZeroFreeTables.tf72f lam x) = 16/(15*lam)
    ∧ (∀ z : ℂ, (Work.ZeroFreeTables.tf72Fc lam z).re
        = (Work.ZeroFreeTables.tf72Fc 1 (z / (lam : ℂ))).re) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsub : (∫ x in (0:ℝ)..(2/lam), x * tf72f lam x)
        = ∫ x in (0:ℝ)..(2/lam), (fun u : ℝ => u * tf72f 1 u) (lam * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show x * tf72f lam x = (lam * x) * tf72f 1 (lam * x)
      rw [tf72f_scale lam hlam x]
      ring
    rw [hsub,
        intervalIntegral.integral_comp_mul_left (fun u : ℝ => u * tf72f 1 u) hlam.ne']
    rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul,
        tf72f_moment_one]
    have hne : lam ≠ 0 := hlam.ne'
    field_simp
  · have hsub : (∫ x in (0:ℝ)..(2/lam), x * Real.exp (lam*x) * tf72f lam x)
        = ∫ x in (0:ℝ)..(2/lam),
            (fun u : ℝ => u * Real.exp u * tf72f 1 u) (lam * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show x * Real.exp (lam*x) * tf72f lam x
        = (lam * x) * Real.exp (lam * x) * tf72f 1 (lam * x)
      rw [tf72f_scale lam hlam x]
      ring
    rw [hsub,
        intervalIntegral.integral_comp_mul_left (fun u : ℝ => u * Real.exp u * tf72f 1 u)
          hlam.ne']
    rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul,
        tf72f_expmoment_one]
    have hne : lam ≠ 0 := hlam.ne'
    field_simp
  · intro z
    rw [tf72Fc_scale lam hlam z]

end Work.ZeroFreeTables.OffAxis
