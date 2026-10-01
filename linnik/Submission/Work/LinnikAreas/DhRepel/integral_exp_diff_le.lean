import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- Pointwise bound: for all reals `a, s, t`,
`exp (a t) - exp ((a - s) t) ≤ s t exp (a t)`.
This is the elementary inequality `1 - x ≤ exp (-x)` multiplied by `exp (a t) > 0` and
rewritten using `exp (a t) exp (-(s t)) = exp ((a - s) t)`. -/
private lemma exp_sub_exp_le (a s t : ℝ) :
    Real.exp (a * t) - Real.exp ((a - s) * t) ≤ s * t * Real.exp (a * t) := by
  have h2 : Real.exp (a * t) * (1 - s * t) ≤ Real.exp ((a - s) * t) := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (s * t))
      (le_of_lt (Real.exp_pos (a * t)))
    rwa [← Real.exp_add, show a * t + -(s * t) = (a - s) * t by ring] at hh
  nlinarith [h2]

/-- The weighted exponential integral bound
`∫_0^L t (L - t) exp (a t) dt ≤ L exp (a L) / a²` for `a > 0`, `L ≥ 0`. -/
private lemma integral_quad_exp_le (a L : ℝ) (ha : 0 < a) (hL : 0 ≤ L) :
    ∫ t in (0:ℝ)..L, t * (L - t) * Real.exp (a * t) ≤ L * Real.exp (a * L) / a ^ 2 := by
  have hderiv : (deriv (fun t : ℝ =>
        Real.exp (a * t) * (-(t^2)/a + (L/a + 2/a^2) * t - L/a^2 - 2/a^3)))
      = (fun x => x * (L - x) * Real.exp (a * x)) := by
    funext x
    change deriv ((fun t : ℝ => Real.exp (a * t)) *
        (fun t : ℝ => (-(t^2)/a + (L/a + 2/a^2) * t - L/a^2 - 2/a^3))) x
        = x * (L - x) * Real.exp (a * x)
    rw [deriv_mul]
    · have hExp : deriv (fun t : ℝ => Real.exp (a * t)) x = Real.exp (a * x) * a := by
        rw [deriv_exp (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => a * t) x)]
        rw [show (fun t : ℝ => a * t) = (fun t : ℝ => a * id t) from rfl]
        rw [deriv_const_mul a differentiableAt_id, deriv_id]
        ring
      have hP : deriv (fun t : ℝ => -(t^2)/a + (L/a + 2/a^2) * t - L/a^2 - 2/a^3) x
          = -(2*x)/a + (L/a + 2/a^2) := by
        rw [deriv_sub_const (2/a^3), deriv_sub_const (L/a^2)]
        change deriv ((fun t : ℝ => -(t^2)/a) + (fun t : ℝ => (L/a + 2/a^2) * t)) x
            = -(2*x)/a + (L/a + 2/a^2)
        rw [deriv_add]
        · have e1 : deriv (fun t : ℝ => -a⁻¹ * (t*t)) x = -a⁻¹ * (x + x) := by
            rw [deriv_const_mul]
            · have hsq : deriv (fun t : ℝ => t*t) x = x + x := by
                change deriv ((fun t : ℝ => t) * (fun t : ℝ => t)) x = x + x
                rw [deriv_mul]
                · simp only [deriv_id'']
                  ring
                · fun_prop
                · fun_prop
              rw [hsq]
            · fun_prop
          rw [show deriv (fun t : ℝ => -(t^2)/a) x
                = deriv (fun t : ℝ => -a⁻¹ * (t*t)) x from by
            congr 1; funext t; ring_nf]
          rw [e1]
          rw [show (fun t : ℝ => (L/a + 2/a^2) * t) = (fun t : ℝ => (L/a + 2/a^2) * id t)
                from rfl]
          rw [deriv_const_mul _ differentiableAt_id, deriv_id]
          rw [div_eq_mul_inv]; ring
        · fun_prop
        · fun_prop
      rw [hExp, hP]
      field_simp
      ring
    · fun_prop
    · fun_prop
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) L,
      DifferentiableAt ℝ (fun t : ℝ =>
        Real.exp (a * t) * (-(t^2)/a + (L/a + 2/a^2) * t - L/a^2 - 2/a^3)) x := by
    intro x _; fun_prop
  have hcont : ContinuousOn (fun x => x * (L - x) * Real.exp (a * x)) (Set.uIcc (0:ℝ) L) := by
    fun_prop
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (fun t : ℝ => Real.exp (a * t) * (-(t^2)/a + (L/a + 2/a^2) * t - L/a^2 - 2/a^3))
    hderiv hdiff hcont
  rw [hFTC]
  have hval : Real.exp (a * L) * (-(L^2)/a + (L/a + 2/a^2) * L - L/a^2 - 2/a^3)
      - Real.exp (a * 0) * (-((0:ℝ)^2)/a + (L/a + 2/a^2) * 0 - L/a^2 - 2/a^3)
      = (Real.exp (a * L) * (a * L - 2) + a * L + 2) / a^3 := by
    rw [mul_zero, Real.exp_zero]; norm_num; field_simp; ring
  rw [hval]
  have h4 : a * L + 2 ≤ 2 * Real.exp (a * L) := by
    have h1 : a * L + 1 ≤ Real.exp (a * L) := Real.add_one_le_exp _
    nlinarith [mul_nonneg ha.le hL]
  have hbound : Real.exp (a * L) * (a * L - 2) + a * L + 2 ≤ a * L * Real.exp (a * L) := by
    nlinarith [h4]
  have ha3 : (0:ℝ) < a^3 := by positivity
  have hstep := div_le_div_of_nonneg_right hbound (le_of_lt ha3)
  have heq : a * L * Real.exp (a * L) / a^3 = L * Real.exp (a * L) / a^2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rwa [heq] at hstep

theorem integral_exp_diff_le (a s L : ℝ) (ha : 0 < a) (hs : 0 ≤ s) (hL : 0 ≤ L) :
    ∫ t in (0:ℝ)..L, (Real.exp (a * t) - Real.exp ((a - s) * t)) * (L - t)
      ≤ s * (L * Real.exp (a * L)) / a ^ 2 := by
  have hmono : ∫ t in (0:ℝ)..L,
        (Real.exp (a * t) - Real.exp ((a - s) * t)) * (L - t)
      ≤ ∫ t in (0:ℝ)..L, (s * t * Real.exp (a * t)) * (L - t) :=
    intervalIntegral.integral_mono_on hL
      (((by fun_prop : Continuous (fun t : ℝ =>
          (Real.exp (a * t) - Real.exp ((a - s) * t)) * (L - t)))).intervalIntegrable 0 L)
      (((by fun_prop : Continuous (fun t : ℝ =>
          (s * t * Real.exp (a * t)) * (L - t)))).intervalIntegrable 0 L)
      (fun t ht => mul_le_mul_of_nonneg_right (exp_sub_exp_le a s t)
        (sub_nonneg.mpr ht.2))
  have hrewrite : ∫ t in (0:ℝ)..L, (s * t * Real.exp (a * t)) * (L - t)
      = s * ∫ t in (0:ℝ)..L, t * (L - t) * Real.exp (a * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  calc ∫ t in (0:ℝ)..L, (Real.exp (a * t) - Real.exp ((a - s) * t)) * (L - t)
      ≤ ∫ t in (0:ℝ)..L, (s * t * Real.exp (a * t)) * (L - t) := hmono
    _ = s * ∫ t in (0:ℝ)..L, t * (L - t) * Real.exp (a * t) := hrewrite
    _ ≤ s * (L * Real.exp (a * L) / a ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_quad_exp_le a L ha hL) hs
    _ = s * (L * Real.exp (a * L)) / a ^ 2 := by ring_nf

end Work.LinnikAreas.DhRepel
