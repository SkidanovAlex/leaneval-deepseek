import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Commons.Analysis.GaussianMeasure

/-- Lower bound for the tail of the one-dimensional Gaussian: for `s ≥ 1`,
`exp(-3π)/s * exp(-π s²) ≤ ∫_{x > s} exp(-π x²)`.

Proof: the integrand is at least `k := exp(-π(s²+3))` on the interval
`[s, s+1/s]` (there `x² ≤ (s+1/s)² = s² + 2 + 1/s² ≤ s² + 3`), and that
interval has length `1/s`, so the tail integral is at least
`k/s = exp(-3π)/s * exp(-π s²)`. -/
theorem gaussian_tail_lower (s : ℝ) (hs : 1 ≤ s) :
    Real.exp (-3 * Real.pi) / s * Real.exp (-Real.pi * s ^ 2)
      ≤ ∫ x in Set.Ioi s, Real.exp (-Real.pi * x ^ 2) := by
  set F : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2) with hF
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hF_cont : Continuous F := by rw [hF]; fun_prop
  have hF_int : IntegrableOn F (Set.Ioi s) := by
    rw [hF]; exact (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
  have hlim := intervalIntegral_tendsto_integral_Ioi s hF_int tendsto_id
  set c : ℝ := Real.exp (-3 * Real.pi) / s * Real.exp (-Real.pi * s ^ 2) with hc
  set k : ℝ := Real.exp (-Real.pi * (s ^ 2 + 3)) with hk
  have hF_nonneg : ∀ u : ℝ, 0 ≤ F u := by
    intro u; rw [hF]; exact (Real.exp_pos _).le
  -- c = k / s
  have hval : c = k / s := by
    rw [hc, hk]
    have h1 : -Real.pi * (s ^ 2 + 3) = -Real.pi * s ^ 2 + (-3 * Real.pi) := by ring
    rw [h1, Real.exp_add]
    field_simp
  -- algebraic bound
  have hb_sq : (s + 1/s)^2 ≤ s^2 + 3 := by
    have hs1 : (1:ℝ) ≤ s^2 := by nlinarith
    have hinv : 1/s^2 ≤ 1 := by
      have := one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) hs1
      simpa using this
    have hsq : (s + 1/s)^2 = s^2 + 2 + 1/s^2 := by
      rw [show (s + 1/s)^2 = s^2 + 2*(s*(1/s)) + (1/s)^2 by ring]
      rw [show s*(1/s) = 1 by field_simp]
      rw [show (1/s)^2 = 1/s^2 by ring]
      ring
    nlinarith
  have hpoint : ∀ x ∈ Set.Icc s (s + 1/s), k ≤ F x := by
    intro x hx
    have hx1 : s ≤ x := hx.1
    have hx2 : x ≤ s + 1/s := hx.2
    have hxpos : 0 ≤ x := le_trans (le_of_lt hs_pos) hx1
    have hx2sq : x^2 ≤ (s + 1/s)^2 := pow_le_pow_left₀ hxpos hx2 2
    have hxsq : x^2 ≤ s^2 + 3 := le_trans hx2sq hb_sq
    have harg : -Real.pi * (s^2 + 3) ≤ -Real.pi * x^2 := by nlinarith [Real.pi_pos]
    rw [hk]
    simp only [hF]
    exact Real.exp_le_exp.mpr harg
  -- ∫_s^{s+1/s} k = c
  have hkb : (∫ x in s..(s + 1/s), (fun _ => k) x) = c := by
    rw [intervalIntegral.integral_const, hval]
    have hbs : s + 1/s - s = 1/s := by ring
    rw [hbs, smul_eq_mul, one_div]
    ring
  -- eventually holds
  have hb : ∀ᶠ M in atTop, c ≤ ∫ x in s..M, F x := by
    filter_upwards [eventually_ge_atTop (s + 1/s)] with M hM
    have hsb : s ≤ s + 1/s := le_add_of_nonneg_right (by positivity)
    have hmono : (∫ x in s..(s + 1/s), (fun _ => k) x) ≤ ∫ x in s..(s + 1/s), F x := by
      refine intervalIntegral.integral_mono_on hsb intervalIntegrable_const
        (hF_cont.intervalIntegrable s (s + 1/s)) ?_
      intro x hx
      exact hpoint x hx
    rw [hkb] at hmono
    have hsplit : (∫ x in s..(s + 1/s), F x) ≤ ∫ x in s..M, F x := by
      have h1 : IntervalIntegrable F volume s (s + 1/s) := hF_cont.intervalIntegrable _ _
      have h2 : IntervalIntegrable F volume (s + 1/s) M := hF_cont.intervalIntegrable _ _
      have hnn : 0 ≤ ∫ x in (s + 1/s)..M, F x :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => hF_nonneg u)
      calc (∫ x in s..(s + 1/s), F x)
          ≤ (∫ x in s..(s + 1/s), F x) + ∫ x in (s + 1/s)..M, F x := le_add_of_nonneg_right hnn
        _ = ∫ x in s..M, F x := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have hmain : c ≤ ∫ x in Set.Ioi s, F x :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hb
  simpa [hc, hF] using hmain

end Commons.Analysis.GaussianMeasure