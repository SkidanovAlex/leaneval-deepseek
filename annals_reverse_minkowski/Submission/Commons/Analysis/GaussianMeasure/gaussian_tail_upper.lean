import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Commons.Analysis.GaussianMeasure

/-- Upper bound for the tail of the one-dimensional Gaussian: for `s > 0`,
`∫_{x > s} exp (-π x²) ≤ exp (-π s²) / (2 π s)`.

Proof idea: on `(s, ∞)` the integrand `F x = exp (-π x²)` is dominated by
`H x = x F x / s` (because `x / s ≥ 1` there), and `H = G'` where
`G x = -F x / (2 π s)`, which vanishes at `+∞`.  Hence
`∫_{s}^{∞} F ≤ ∫_{s}^{∞} H = F s / (2 π s)`. -/
theorem gaussian_tail_upper (s : ℝ) (hs : 0 < s) :
    (∫ x in Set.Ioi s, Real.exp (-Real.pi * x ^ 2))
      ≤ Real.exp (-Real.pi * s ^ 2) / (2 * Real.pi * s) := by
  set F : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2) with hF
  set c : ℝ := 2 * Real.pi * s with hc
  have hc_pos : 0 < c := by rw [hc]; positivity
  have hs_ne : s ≠ 0 := ne_of_gt hs
  set G : ℝ → ℝ := fun x => -(F x) / c with hG
  set H : ℝ → ℝ := fun x => x * F x / s with hH
  -- derivative of `F`
  have hderivF : ∀ x, HasDerivAt F (-(2 * Real.pi * x) * F x) x := by
    intro x
    have h_inner : HasDerivAt (fun y : ℝ => -Real.pi * y ^ 2) (-(2 * Real.pi * x)) x := by
      have h : HasDerivAt (fun y : ℝ => -Real.pi * y ^ 2) (-Real.pi * (2 * x)) x := by
        have h0 := (hasDerivAt_pow 2 x).const_mul (-Real.pi)
        simpa using h0
      rwa [show -Real.pi * (2 * x) = -(2 * Real.pi * x) by ring] at h
    have h_exp : HasDerivAt (fun y : ℝ => Real.exp (-Real.pi * y ^ 2))
        (Real.exp (-Real.pi * x ^ 2) * (-(2 * Real.pi * x))) x := h_inner.exp
    have h_exp' : HasDerivAt F (F x * (-(2 * Real.pi * x))) x := by
      simpa [hF] using h_exp
    rwa [show F x * (-(2 * Real.pi * x)) = -(2 * Real.pi * x) * F x by ring] at h_exp'
  -- derivative of `G` is `H`
  have hderivG : ∀ x, HasDerivAt G (H x) x := by
    intro x
    have h1 := (hderivF x).neg.div_const c
    have h2 : HasDerivAt G (2 * Real.pi * x * F x / c) x := by
      rw [hG]; simpa using h1
    have hval : 2 * Real.pi * x * F x / c = H x := by
      rw [hH, hc]
      rw [div_eq_div_iff (by positivity : 2 * Real.pi * s ≠ 0) hs_ne]
      ring
    rwa [hval] at h2
  -- continuity
  have hF_cont : Continuous F := by
    rw [hF]; fun_prop
  have hH_cont : Continuous H := by
    rw [hH]
    exact (continuous_id.mul hF_cont).div_const s
  -- integrability of `F` on `(s, ∞)`
  have hF_int : IntegrableOn F (Set.Ioi s) := by
    rw [hF]
    exact (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
  -- the finite-interval bound
  have hbound : ∀ᶠ M in atTop, (∫ x in s..M, F x) ≤ F s / c := by
    filter_upwards [eventually_ge_atTop s] with M hMs
    have hmono : (∫ x in s..M, F x) ≤ ∫ x in s..M, H x := by
      refine intervalIntegral.integral_mono_on hMs (hF_cont.intervalIntegrable s M)
        (hH_cont.intervalIntegrable s M) ?_
      intro x hx
      have hxF : 0 ≤ F x := by rw [hF]; exact (Real.exp_pos _).le
      have h1 : (1 : ℝ) ≤ x / s := by
        rw [le_div_iff₀ hs]; simpa using hx.1
      have hHx : H x = (x / s) * F x := by rw [hH]; ring
      calc F x = 1 * F x := by ring
        _ ≤ (x / s) * F x := mul_le_mul_of_nonneg_right h1 hxF
        _ = H x := hHx.symm
    have hFTC : (∫ x in s..M, H x) = G M - G s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := M)
        (f := G) (f' := H) (fun x _ => hderivG x) (hH_cont.intervalIntegrable s M)
    have hGM : G M = -(F M) / c := by rw [hG]
    have hGs : G s = -(F s) / c := by rw [hG]
    have hFM : 0 ≤ F M := by rw [hF]; exact (Real.exp_pos _).le
    calc (∫ x in s..M, F x) ≤ ∫ x in s..M, H x := hmono
      _ = G M - G s := hFTC
      _ = (F s - F M) / c := by rw [hGM, hGs]; ring
      _ ≤ F s / c := by
          apply div_le_div_of_nonneg_right _ hc_pos.le
          linarith
  -- take the limit `M → ∞`
  have hlim := intervalIntegral_tendsto_integral_Ioi s hF_int tendsto_id
  have hres : (∫ x in Set.Ioi s, F x) ≤ F s / c :=
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbound
  simpa [hF] using hres

end Commons.Analysis.GaussianMeasure