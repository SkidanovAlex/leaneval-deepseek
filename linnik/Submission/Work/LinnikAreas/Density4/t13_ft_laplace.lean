/-
# Area 4 / HB §12 — the Laplace transform of Heath-Brown's §7 test function

The closed form of `F(z) = ∫₀^{2γ} e^{-zt} f(t) dt` (HB §7 / Table 13).  Everything here is
self-contained: the three elementary trigonometric/Laplace integrals used in the assembly are
(auxiliary copies of) the lemmas of `integral_exp_neg_cos`, `integral_exp_neg_sin` and
`integral_mul_exp_neg_cos`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.integral_exp_neg_cos
import Submission.Work.LinnikAreas.Density4.integral_exp_neg_sin

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

namespace Work.LinnikAreas.Density4

/-! ## Elementary integrals (self-contained auxiliary copies) -/

/-- `∫₀^T e^{-zt} dt = (1 - e^{-zT})/z` for `z ≠ 0`. -/
theorem integral_exp_neg_zero_T_aux (z T : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..T, Real.exp (-(z*t)) = (1 - Real.exp (-(z*T)))/z := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun t : ℝ => -Real.exp (-(z*t))) (z * Real.exp (-(z*x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => -(z*t)) (-z) x := by
      have := (hasDerivAt_id x).const_mul (-z)
      simpa [neg_mul] using this
    have h3 : HasDerivAt (fun t : ℝ => -Real.exp (-(z*t))) (-(Real.exp (-(z*x)) * (-z))) x :=
      h1.exp.neg
    have hval : -(Real.exp (-(z*x)) * (-z)) = z * Real.exp (-(z*x)) := by ring
    rwa [hval] at h3
  have hint : IntervalIntegrable (fun x : ℝ => z * Real.exp (-(z*x))) volume (0:ℝ) T :=
    (by fun_prop : Continuous fun x : ℝ => z * Real.exp (-(z*x))).intervalIntegrable _ _
  have key : z * (∫ t in (0:ℝ)..T, Real.exp (-(z*t))) = 1 - Real.exp (-(z*T)) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_neg_eq_add]
    ring
  rw [eq_div_iff hz, mul_comm (∫ t in (0:ℝ)..T, Real.exp (-(z*t))) z]
  exact key

/-- `∫₀^T t e^{-zt} dt = (1 - e^{-zT}(1+Tz))/z²` for `z ≠ 0`. -/
theorem integral_mul_exp_neg_zero_T_aux (z T : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..T, t * Real.exp (-(z*t)) = (1 - Real.exp (-(z*T))*(1 + T*z))/z^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun t : ℝ => -(z*t + 1) * Real.exp (-(z*t)))
        (z^2 * (x * Real.exp (-(z*x)))) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => z*t + 1) z x := by
      simpa using ((hasDerivAt_id x).const_mul z).add_const 1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(z*t))) (Real.exp (-(z*x)) * (-z)) x := by
      have h3 : HasDerivAt (fun t : ℝ => -(z*t)) (-z) x := by
        have := (hasDerivAt_id x).const_mul (-z)
        simpa [neg_mul] using this
      exact h3.exp
    have h4 := h1.neg.mul h2
    exact h4.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hint : IntervalIntegrable (fun x : ℝ => z^2 * (x * Real.exp (-(z*x)))) volume (0:ℝ) T :=
    (by fun_prop : Continuous fun x : ℝ => z^2 * (x * Real.exp (-(z*x)))).intervalIntegrable _ _
  have key : z^2 * (∫ t in (0:ℝ)..T, t * Real.exp (-(z*t)))
      = 1 - Real.exp (-(z*T))*(1 + T*z) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  rw [eq_div_iff (pow_ne_zero 2 hz), mul_comm (∫ t in (0:ℝ)..T, t * Real.exp (-(z*t))) (z^2)]
  exact key

/-- `∫₀^T t e^{-zt} cos(ζt) dt = e^{-zT}((-zT/(z²+ζ²) + (ζ²-z²)/(z²+ζ²)²)cos(ζT)
+ (ζT/(z²+ζ²) + 2ζz/(z²+ζ²)²)sin(ζT)) - (ζ²-z²)/(z²+ζ²)²`. -/
theorem integral_mul_exp_neg_cos_aux (z ζ T : ℝ) (hW : z ^ 2 + ζ ^ 2 ≠ 0) :
    ∫ t in (0:ℝ)..T, t * Real.exp (-(z * t)) * Real.cos (ζ * t)
      = Real.exp (-(z * T)) *
          ((-(z * T) / (z ^ 2 + ζ ^ 2) + (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2)
              * Real.cos (ζ * T)
            + (ζ * T / (z ^ 2 + ζ ^ 2) + 2 * ζ * z / (z ^ 2 + ζ ^ 2) ^ 2)
              * Real.sin (ζ * T))
        - (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2 := by
  let F : ℝ → ℝ := fun t => Real.exp (-(z*t)) *
      (((-z/(z^2+ζ^2))*t + (ζ^2 - z^2)/(z^2+ζ^2)^2) * Real.cos (ζ*t)
        + ((ζ/(z^2+ζ^2))*t + 2*ζ*z/(z^2+ζ^2)^2) * Real.sin (ζ*t))
  have hderiv : ∀ t : ℝ, HasDerivAt F (t * Real.exp (-(z*t)) * Real.cos (ζ*t)) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Real.exp (-(z*t))) (Real.exp (-(z*t))*(-z)) t := by
      have h : HasDerivAt (fun t : ℝ => (-z)*t) (-z) t := hasDerivAt_const_mul (x := t) (-z)
      have h' : HasDerivAt (fun t : ℝ => -(z*t)) (-z) t := by simpa only [neg_mul] using h
      exact h'.exp
    have hp : HasDerivAt (fun t : ℝ => (-z/(z^2+ζ^2))*t + (ζ^2 - z^2)/(z^2+ζ^2)^2)
        (-z/(z^2+ζ^2)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-z/(z^2+ζ^2))).add_const ((ζ^2 - z^2)/(z^2+ζ^2)^2)
    have hq : HasDerivAt (fun t : ℝ => (ζ/(z^2+ζ^2))*t + 2*ζ*z/(z^2+ζ^2)^2)
        (ζ/(z^2+ζ^2)) t := by
      simpa using ((hasDerivAt_id t).const_mul (ζ/(z^2+ζ^2))).add_const (2*ζ*z/(z^2+ζ^2)^2)
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (ζ*t)) (-Real.sin (ζ*t)*ζ) t :=
      (hasDerivAt_const_mul (x := t) ζ).cos
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (ζ*t)) (Real.cos (ζ*t)*ζ) t :=
      (hasDerivAt_const_mul (x := t) ζ).sin
    have hG := (hp.mul hcos).add (hq.mul hsin)
    have hF := he.mul hG
    refine hF.congr_deriv ?_
    simp only [Pi.add_apply, Pi.mul_apply]
    field_simp
    ring
  have hcont : IntervalIntegrable (fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (ζ*t))
      volume (0:ℝ) T :=
    (by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (ζ*t)).intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := T)
      (f := F) (f' := fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (ζ*t))
      (fun t _ => hderiv t) hcont
  rw [key]
  simp only [F, mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero,
    mul_one, zero_add, add_zero]
  field_simp

/-- Linearity of the interval integral for a five-term linear combination of continuous
integrands. -/
theorem integral_lin5_aux (a b : ℝ) (c0 c1 c2 c3 c4 : ℝ) {f0 f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : IntervalIntegrable f0 volume a b) (h1 : IntervalIntegrable f1 volume a b)
    (h2 : IntervalIntegrable f2 volume a b) (h3 : IntervalIntegrable f3 volume a b)
    (h4 : IntervalIntegrable f4 volume a b) :
    ∫ x in a..b, (c0 * f0 x + c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x)
      = c0 * (∫ x in a..b, f0 x) + c1 * (∫ x in a..b, f1 x) + c2 * (∫ x in a..b, f2 x)
        + c3 * (∫ x in a..b, f3 x) + c4 * (∫ x in a..b, f4 x) := by
  have h01 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x) volume a b :=
    (h0.const_mul c0).add (h1.const_mul c1)
  have h012 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x + c2 * f2 x) volume a b :=
    h01.add (h2.const_mul c2)
  have h0123 : IntervalIntegrable (fun x => c0 * f0 x + c1 * f1 x + c2 * f2 x + c3 * f3 x)
      volume a b := h012.add (h3.const_mul c3)
  rw [intervalIntegral.integral_add h0123 (h4.const_mul c4)]
  rw [intervalIntegral.integral_add h012 (h3.const_mul c3)]
  rw [intervalIntegral.integral_add h01 (h2.const_mul c2)]
  rw [intervalIntegral.integral_add (h0.const_mul c0) (h1.const_mul c1)]
  simp only [intervalIntegral.integral_const_mul]

/-- Pointwise expansion of the `fT` integrand into the five elementary integrals. -/
theorem testfun_integrand_expand_aux (θ γ ζ z t : ℝ) :
    Real.exp (-(z*t)) * ((2*γ - t) * (Real.cos (ζ*t)/2 + Real.cos θ^2)
        + Real.sin (2*θ - ζ*t)/(2*ζ) - Real.sin (2*θ)/ζ
        + 2*Real.cos θ*Real.sin (ζ*t - θ)/ζ)
  = (2*γ*Real.cos θ^2 - Real.sin (2*θ)/ζ) * Real.exp (-(z*t))
    + (γ - Real.sin (2*θ)/(2*ζ)) * (Real.exp (-(z*t)) * Real.cos (ζ*t))
    - Real.cos θ^2 * (t * Real.exp (-(z*t)))
    - (1/2) * (t * Real.exp (-(z*t)) * Real.cos (ζ*t))
    + (1/2 + Real.cos θ^2)/ζ * (Real.exp (-(z*t)) * Real.sin (ζ*t)) := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-! ## The main theorem -/

theorem t13_ft_laplace (θ lam z : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) (hz : z ≠ 0) :
    Work.LinnikAreas.Density4.FT θ lam z =
      lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
      ( (2 * Work.LinnikAreas.Density4.gammaT θ lam * Real.cos θ ^ 2
            - Real.sin (2 * θ) / Work.LinnikAreas.Density4.zetaT θ lam)
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))) / z)
        - Real.cos θ ^ 2
          * ((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
              * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)) / z ^ 2)
        + (Work.LinnikAreas.Density4.gammaT θ lam
            - Real.sin (2 * θ) / (2 * Work.LinnikAreas.Density4.zetaT θ lam))
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * z
              + Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * Work.LinnikAreas.Density4.zetaT θ lam)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2))
        - (1/2)
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * (Real.cos (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)
                  + Real.sin (2 * θ) * (2 * θ)))
              * (z ^ 2 - Work.LinnikAreas.Density4.zetaT θ lam ^ 2)
              - (Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                  * (Real.cos (2 * θ) * (2 * θ)
                    - Real.sin (2 * θ) * (1 + 2 * Work.LinnikAreas.Density4.gammaT θ lam * z)))
                * (2 * Work.LinnikAreas.Density4.zetaT θ lam * z))
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2) ^ 2)
        + (1/2 + Real.cos θ ^ 2) / Work.LinnikAreas.Density4.zetaT θ lam
          * (((1 - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.cos (2 * θ)) * Work.LinnikAreas.Density4.zetaT θ lam
              - Real.exp (-(2 * Work.LinnikAreas.Density4.gammaT θ lam * z))
                * Real.sin (2 * θ) * z)
              / (z ^ 2 + Work.LinnikAreas.Density4.zetaT θ lam ^ 2)) ) := by
  have hγpos : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  have hζpos : 0 < zetaT θ lam := zetaT_pos hθ1 hθ2 hlam
  have hζne : zetaT θ lam ≠ 0 := ne_of_gt hζpos
  have hWne : z ^ 2 + zetaT θ lam ^ 2 ≠ 0 := by
    have h : 0 < z ^ 2 + zetaT θ lam ^ 2 := by
      nlinarith [sq_nonneg z, pow_pos hζpos 2]
    exact ne_of_gt h
  have hγζ : gammaT θ lam * zetaT θ lam = θ := by rw [gammaT]; field_simp
  set c0 := 2 * gammaT θ lam * Real.cos θ ^ 2 - Real.sin (2 * θ) / zetaT θ lam with hc0
  set c1 := gammaT θ lam - Real.sin (2 * θ) / (2 * zetaT θ lam) with hc1
  set c4 := (1/2 + Real.cos θ ^ 2) / zetaT θ lam with hc4
  have hf0 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z*t))) volume (0:ℝ) (2 * gammaT θ lam) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t))).intervalIntegrable _ _
  have hf1 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
      volume (0:ℝ) (2 * gammaT θ lam) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)).intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun t : ℝ => t * Real.exp (-(z*t))) volume (0:ℝ) (2 * gammaT θ lam) :=
    (by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(z*t))).intervalIntegrable _ _
  have hf3 : IntervalIntegrable (fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t))
      volume (0:ℝ) (2 * gammaT θ lam) :=
    (by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)).intervalIntegrable _ _
  have hf4 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t))
      volume (0:ℝ) (2 * gammaT θ lam) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t)).intervalIntegrable _ _
  -- the five elementary integrals, instantiated at `T = 2γ`
  have hI1 : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t))
      = (1 - Real.exp (-(2 * gammaT θ lam * z))) / z := by
    rw [integral_exp_neg_zero_T_aux z (2 * gammaT θ lam) hz,
      show z * (2 * gammaT θ lam) = 2 * gammaT θ lam * z by ring]
  have hIt : ∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t))
      = (1 - Real.exp (-(2 * gammaT θ lam * z)) * (1 + 2 * gammaT θ lam * z)) / z ^ 2 := by
    rw [integral_mul_exp_neg_zero_T_aux z (2 * gammaT θ lam) hz,
      show z * (2 * gammaT θ lam) = 2 * gammaT θ lam * z by ring]
  have hIc : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)
      = ((1 - Real.exp (-(2 * gammaT θ lam * z)) * Real.cos (2 * θ)) * z
          + Real.exp (-(2 * gammaT θ lam * z)) * Real.sin (2 * θ) * zetaT θ lam)
        / (z ^ 2 + zetaT θ lam ^ 2) := by
    rw [integral_exp_neg_cos z (zetaT θ lam) (2 * gammaT θ lam) hWne,
      show z * (2 * gammaT θ lam) = 2 * gammaT θ lam * z by ring,
      show (2 * gammaT θ lam) * zetaT θ lam = 2 * θ by
        rw [show (2 * gammaT θ lam) * zetaT θ lam = 2 * (gammaT θ lam * zetaT θ lam) by ring, hγζ]]
  have hIs : ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * Real.sin (zetaT θ lam*t)
      = ((1 - Real.exp (-(2 * gammaT θ lam * z)) * Real.cos (2 * θ)) * zetaT θ lam
          - Real.exp (-(2 * gammaT θ lam * z)) * Real.sin (2 * θ) * z)
        / (z ^ 2 + zetaT θ lam ^ 2) := by
    rw [integral_exp_neg_sin z (zetaT θ lam) (2 * gammaT θ lam) hWne,
      show z * (2 * gammaT θ lam) = 2 * gammaT θ lam * z by ring,
      show (2 * gammaT θ lam) * zetaT θ lam = 2 * θ by
        rw [show (2 * gammaT θ lam) * zetaT θ lam = 2 * (gammaT θ lam * zetaT θ lam) by ring, hγζ]]
  have hItc : ∫ t in (0:ℝ)..(2 * gammaT θ lam), t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam*t)
      = Real.exp (-(z * (2 * gammaT θ lam))) *
          ((-(z * (2 * gammaT θ lam)) / (z ^ 2 + zetaT θ lam ^ 2)
              + (zetaT θ lam ^ 2 - z ^ 2) / (z ^ 2 + zetaT θ lam ^ 2) ^ 2)
              * Real.cos (zetaT θ lam * (2 * gammaT θ lam))
            + (zetaT θ lam * (2 * gammaT θ lam) / (z ^ 2 + zetaT θ lam ^ 2)
              + 2 * zetaT θ lam * z / (z ^ 2 + zetaT θ lam ^ 2) ^ 2)
              * Real.sin (zetaT θ lam * (2 * gammaT θ lam)))
        - (zetaT θ lam ^ 2 - z ^ 2) / (z ^ 2 + zetaT θ lam ^ 2) ^ 2 := by
    rw [integral_mul_exp_neg_cos_aux z (zetaT θ lam) (2 * gammaT θ lam) hWne]
  -- step 1: `FT` reduces to `λ²(1+tan²θ)² · ∫₀^{2γ} e^{-zt} h(t)`
  have h1 : FT θ lam z = lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
      (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) *
        ((2 * gammaT θ lam - t) * (Real.cos (zetaT θ lam * t) / 2 + Real.cos θ ^ 2)
          + Real.sin (2 * θ - zetaT θ lam * t) / (2 * zetaT θ lam)
          - Real.sin (2 * θ) / zetaT θ lam
          + 2 * Real.cos θ * Real.sin (zetaT θ lam * t - θ) / zetaT θ lam)) := by
    rw [FT]
    rw [show (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) * fT θ lam t)
          = ∫ t in (0:ℝ)..(2 * gammaT θ lam), lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
              (Real.exp (-(z*t)) *
                ((2 * gammaT θ lam - t) * (Real.cos (zetaT θ lam * t) / 2 + Real.cos θ ^ 2)
                  + Real.sin (2 * θ - zetaT θ lam * t) / (2 * zetaT θ lam)
                  - Real.sin (2 * θ) / zetaT θ lam
                  + 2 * Real.cos θ * Real.sin (zetaT θ lam * t - θ) / zetaT θ lam)) from
      intervalIntegral.integral_congr (fun t ht => by
        have ht' : 0 ≤ t ∧ t ≤ 2 * gammaT θ lam := by
          rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 2 * gammaT θ lam)] at ht
          exact ht
        rw [fT, if_pos ht']
        ring)]
    rw [intervalIntegral.integral_const_mul]
  -- step 2: the elementary integrals assemble into the stated closed form
  have h2 : (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) *
        ((2 * gammaT θ lam - t) * (Real.cos (zetaT θ lam * t) / 2 + Real.cos θ ^ 2)
          + Real.sin (2 * θ - zetaT θ lam * t) / (2 * zetaT θ lam)
          - Real.sin (2 * θ) / zetaT θ lam
          + 2 * Real.cos θ * Real.sin (zetaT θ lam * t - θ) / zetaT θ lam))
      = ( (c0)
          * ((1 - Real.exp (-(2 * gammaT θ lam * z))) / z)
        - Real.cos θ ^ 2
          * ((1 - Real.exp (-(2 * gammaT θ lam * z))
              * (1 + 2 * gammaT θ lam * z)) / z ^ 2)
        + (c1)
          * (((1 - Real.exp (-(2 * gammaT θ lam * z))
                * Real.cos (2 * θ)) * z
              + Real.exp (-(2 * gammaT θ lam * z))
                * Real.sin (2 * θ) * zetaT θ lam)
              / (z ^ 2 + zetaT θ lam ^ 2))
        - (1/2)
          * (((1 - Real.exp (-(2 * gammaT θ lam * z))
                * (Real.cos (2 * θ) * (1 + 2 * gammaT θ lam * z)
                  + Real.sin (2 * θ) * (2 * θ)))
              * (z ^ 2 - zetaT θ lam ^ 2)
              - (Real.exp (-(2 * gammaT θ lam * z))
                  * (Real.cos (2 * θ) * (2 * θ)
                    - Real.sin (2 * θ) * (1 + 2 * gammaT θ lam * z)))
                * (2 * zetaT θ lam * z))
              / (z ^ 2 + zetaT θ lam ^ 2) ^ 2)
        + (c4)
          * (((1 - Real.exp (-(2 * gammaT θ lam * z))
                * Real.cos (2 * θ)) * zetaT θ lam
              - Real.exp (-(2 * gammaT θ lam * z))
                * Real.sin (2 * θ) * z)
              / (z ^ 2 + zetaT θ lam ^ 2)) ) := by
    rw [show (∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z*t)) *
        ((2 * gammaT θ lam - t) * (Real.cos (zetaT θ lam * t) / 2 + Real.cos θ ^ 2)
          + Real.sin (2 * θ - zetaT θ lam * t) / (2 * zetaT θ lam)
          - Real.sin (2 * θ) / zetaT θ lam
          + 2 * Real.cos θ * Real.sin (zetaT θ lam * t - θ) / zetaT θ lam))
        = ∫ t in (0:ℝ)..(2 * gammaT θ lam),
            ( c0 * Real.exp (-(z*t))
              + c1 * (Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t))
              + (-Real.cos θ ^ 2) * (t * Real.exp (-(z*t)))
              + (-(1/2)) * (t * Real.exp (-(z*t)) * Real.cos (zetaT θ lam * t))
              + c4 * (Real.exp (-(z*t)) * Real.sin (zetaT θ lam * t)) ) from
      intervalIntegral.integral_congr (fun t ht => by
        rw [testfun_integrand_expand_aux θ (gammaT θ lam) (zetaT θ lam) z t,
          ← hc0, ← hc1, ← hc4]
        ring)]
    rw [integral_lin5_aux (0:ℝ) (2 * gammaT θ lam) c0 c1 (-Real.cos θ ^ 2) (-(1/2)) c4
        hf0 hf1 hf2 hf3 hf4]
    rw [hI1, hIt, hIc, hIs, hItc]
    rw [hc0, hc1, hc4]
    rw [show z * (2 * gammaT θ lam) = 2 * gammaT θ lam * z by ring]
    rw [show zetaT θ lam * (2 * gammaT θ lam) = 2 * (gammaT θ lam * zetaT θ lam) by ring]
    rw [show (2:ℝ) * θ = 2 * (gammaT θ lam * zetaT θ lam) by rw [hγζ]]
    field_simp
    ring
  rw [h1, h2, hc0, hc1, hc4]

end Work.LinnikAreas.Density4
