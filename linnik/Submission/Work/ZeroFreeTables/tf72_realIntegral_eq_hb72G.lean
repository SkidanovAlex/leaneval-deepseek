import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.t23Defs

/-!
# `tf72_realIntegral_eq_hb72G` — the Laplace transform of HB Lemma 7.2's test function

Heath-Brown (1992), Lemma 7.2: the test function `f = g ∗ g` of the variational
problem of §7 is, on `[0, 2/λ]`, the polynomial

  `f t = (λ/30) (2 − λt)³ (4 + 6λt + λ²t²)`,

while HB's normalised density is `g(u) = 32 − 40u² + 20u³ − u⁵ = (2−u)³(4+6u+u²)`
with Laplace-type transform `G(x) = ∫₀² g(u) e^{xu} du` (`hb72g`, `hb72G`).

The substitution `u = λt` in the real Laplace integral of `f` cancels the factor
`λ` and gives, for `λ > 0` and every real `z`,

  `∫₀^{2/λ} e^{−zt} f(t) dt = G(−z/λ)/30`.

This is the identification used to turn the `F`-expressions of HB Tables 2 and 3 into
functions of the rational data `(λ, b, v)` alone (combined with
`tf72Fc_re_eq_realIntegral`, which identifies `Re F` with this real integral).
-/

noncomputable section
namespace Work.ZeroFreeTables

theorem tf72_realIntegral_eq_hb72G (lam z : ℝ) (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * Work.ZeroFreeTables.tf72f lam t)
      = Work.ZeroFreeTables.hb72G (-z/lam) / 30 := by
  have hne : lam ≠ 0 := hlam.ne'
  -- On `[0, 2/λ]` the test function `f` is the explicit polynomial (Lemma 7.2).
  have hpoly : (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * Work.ZeroFreeTables.tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 2/lam by positivity)] at ht
    rw [Work.ZeroFreeTables.tf72f_eq_poly lam hlam t ht]
  rw [hpoly]
  -- Rewrite the integrand as `H (λ t)` for the canonical density `H`.
  have hsub : (∫ t in (0:ℝ)..(2/lam),
        Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)))
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => (lam/30)*(Real.exp (((-z)/lam)*u)*((2-u)^3*(4+6*u+u^2)))) (lam*t) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    have hzt : ((-z)/lam)*(lam*t) = -(z*t) := by field_simp
    rw [hzt]
    ring
  rw [hsub]
  -- Substitution `u = λ t` (`intervalIntegral.integral_comp_mul_left`).
  rw [intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => (lam/30)*(Real.exp (((-z)/lam)*u)*((2-u)^3*(4+6*u+u^2)))) hne]
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  -- Identify the polynomial with `hb72g` (they are the same expanded polynomial).
  have hX : (∫ u in (0:ℝ)..2, Real.exp (((-z)/lam)*u)*((2-u)^3*(4+6*u+u^2)))
      = ∫ u in (0:ℝ)..2, Work.ZeroFreeTables.hb72g u * Real.exp (((-z)/lam)*u) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [Work.ZeroFreeTables.hb72g]; ring
  rw [hX, Work.ZeroFreeTables.hb72G]
  -- The scales `λ` cancel against the Jacobian `1/λ`.
  have hscal : ∀ Z : ℝ, lam⁻¹ * (lam/30 * Z) = Z/30 := by intro Z; field_simp
  rw [hscal]

end Work.ZeroFreeTables
