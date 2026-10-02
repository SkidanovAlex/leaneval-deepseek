import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral `∫₀^{2π} dθ / (a² + 1/4 - a cos θ)`

We prove

`(2π)⁻¹ ∫₀^{2π} (a² + 1/4 - a cos θ)⁻¹ dθ = 1 / |a² - 1/4|`   for `a² ≠ 1/4`.

The integral is the Poisson integral of the Poisson kernel `(1-p²)/(1-2p cos θ + p²)` for a
suitable `p` with `|p| < 1`.  Concretely, with `A = a² + 1/4`, `B = a` and `√(A²-B²) = |a²-1/4|`,

* if `a² < 1/4` then `p = 2a`,
* if `a² > 1/4` then `p = 1/(2a)`,

and in both cases `A - B cos θ = |a²-1/4| · (1 - 2p cos θ + p²)/(1 - p²)`.

The Poisson integral `∫₀^{2π} (1-p²)/(1-2p cos θ+p²) dθ = 2π` (`|p| < 1`) is obtained from the
classical Poisson integral formula for harmonic functions (`HarmonicOnNhd.circleAverage_poissonKernel_smul`)
applied to the constant harmonic function `1` on the unit disk.
-/

open Real MeasureTheory Complex InnerProductSpace Metric

namespace Work.PTGeometric.RieszProj

/-- The denominator `1 - 2 p cos θ + p²` of the Poisson kernel is positive when `|p| < 1`. -/
lemma one_sub_two_mul_cos_add_sq_pos (p θ : ℝ) (hp : |p| < 1) :
    0 < 1 - 2*p*Real.cos θ + p^2 := by
  have hle : p * Real.cos θ ≤ |p| := by
    calc p * Real.cos θ ≤ |p * Real.cos θ| := le_abs_self _
      _ = |p| * |Real.cos θ| := abs_mul p _
      _ ≤ |p| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg p)
      _ = |p| := mul_one _
  have hsp : |p| ^ 2 = p ^ 2 := sq_abs p
  have h1 : 0 < 1 - |p| := by linarith
  have h2 : 0 < (1 - |p|)^2 := pow_pos h1 2
  nlinarith [hle, hsp, h2]

/-- The Poisson kernel integral: for `|p| < 1`,
`(2π)⁻¹ ∫₀^{2π} (1-p²)/(1-2p cos θ + p²) dθ = 1`. -/
lemma poisson_kernel_integral (p : ℝ) (hp : |p| < 1) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi), (1 - p^2)/(1 - 2*p*Real.cos θ + p^2) = 1 := by
  have hker : ∀ θ : ℝ, poissonKernel (0:ℂ) (p:ℂ) (circleMap 0 1 θ) =
      (1 - p^2)/(1 - 2*p*Real.cos θ + p^2) := by
    intro θ
    have hzn : ‖Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
    have hden : ‖Complex.exp ((θ:ℂ) * Complex.I) - (p:ℂ)‖^2 = 1 - 2*p*Real.cos θ + p^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, add_zero,
        sub_zero, mul_zero, mul_one]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have hz : circleMap 0 1 θ = Complex.exp ((θ:ℂ) * Complex.I) := by
      rw [circleMap_zero, Complex.ofReal_one, one_mul]
    rw [poissonKernel_def, hz]
    simp only [sub_zero, hzn, Complex.sq_norm, Complex.normSq_ofReal, hden]
    ring
  have hfun : (fun θ : ℝ => (poissonKernel (0:ℂ) (p:ℂ) • (fun _ : ℂ => (1:ℝ))) (circleMap 0 1 θ))
      = (fun θ : ℝ => (1 - p^2)/(1 - 2*p*Real.cos θ + p^2)) := by
    funext θ
    rw [smul_eq_mul, Pi.mul_apply, mul_one]
    exact hker θ
  have hf : HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (Metric.closedBall (0:ℂ) 1) :=
    harmonicOnNhd_const 1
  have hw : (p:ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    simpa using hp
  have h := HarmonicOnNhd.circleAverage_poissonKernel_smul (f := fun _ : ℂ => (1:ℝ)) hf hw
  rw [Real.circleAverage_def] at h
  rw [hfun] at h
  simpa using h

/-- Analytic conversion step: if `X = q · Y/(1-p²)` with all relevant factors nonzero then
`X⁻¹ = q⁻¹ · (1-p²)/Y`. -/
lemma inv_of_eq_mul_div (X q Y p : ℝ) (hrel : X = q * (Y/(1-p^2))) (hq : q ≠ 0) (hY : Y ≠ 0)
    (hp2 : 1-p^2 ≠ 0) : X⁻¹ = (1/q) * ((1-p^2)/Y) := by
  rw [hrel]
  field_simp

theorem inv_integral_cos (a : ℝ) (ha : a ^ 2 ≠ 1/4) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹
      = 1 / |a ^ 2 - 1/4| := by
  have hpois_int : ∀ p : ℝ, |p| < 1 →
      ∫ θ in (0:ℝ)..(2*Real.pi), (1 - p^2)/(1 - 2*p*Real.cos θ + p^2) = 2*Real.pi := by
    intro p hp
    have h0 := poisson_kernel_integral p hp
    have h2pi : (2*(Real.pi:ℝ)) ≠ 0 := by positivity
    have h1 := congrArg (fun x : ℝ => (2*Real.pi) * x) h0
    simp only [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul, mul_one] at h1
    exact h1
  have h1mp2 : ∀ p : ℝ, |p| < 1 → (1 - p^2) ≠ 0 := by
    intro p hp
    have h : p^2 < 1 := by
      have hh := abs_lt.mp hp
      nlinarith [hh.1, hh.2]
    intro hc; nlinarith
  have hq : |a^2 - 1/4| ≠ 0 := abs_ne_zero.mpr (by intro h; exact ha (by linarith [h]))
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · -- case `a² < 1/4`, `p = 2a`
    have hp : |2*a| < 1 := by
      have : (2*a)^2 < 1^2 := by nlinarith [hlt]
      simpa using (sq_lt_sq.mp this)
    have hrel : ∀ θ : ℝ, a^2+1/4-a*Real.cos θ =
        |a^2-1/4| * ((1-2*(2*a)*Real.cos θ+(2*a)^2)/(1-(2*a)^2)) := by
      intro θ
      have hd' : (1:ℝ) - 4*a^2 ≠ 0 := by nlinarith [hlt]
      rw [abs_of_neg (by linarith : a^2 - 1/4 < 0)]
      rw [show (1-2*(2*a)*Real.cos θ+(2*a)^2) = (1-4*a*Real.cos θ+4*a^2) from by ring,
          show (1-(2*a)^2) = (1-4*a^2) from by ring,
          ← mul_div_assoc, eq_div_iff hd']
      ring
    have hpt : ∀ θ : ℝ, (a^2+1/4-a*Real.cos θ)⁻¹ =
        (1/|a^2-1/4|)*((1-(2*a)^2)/(1-2*(2*a)*Real.cos θ+(2*a)^2)) := by
      intro θ
      exact inv_of_eq_mul_div _ _ _ _ (hrel θ) hq
        (one_sub_two_mul_cos_add_sq_pos (2*a) θ hp).ne' (h1mp2 (2*a) hp)
    calc (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi), (a^2+1/4-a*Real.cos θ)⁻¹
        = (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi),
            (1/|a^2-1/4|)*((1-(2*a)^2)/(1-2*(2*a)*Real.cos θ+(2*a)^2)) := by
          congr 1
          exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
      _ = (2*Real.pi)⁻¹ * ((1/|a^2-1/4|) *
            ∫ θ in (0:ℝ)..(2*Real.pi), (1-(2*a)^2)/(1-2*(2*a)*Real.cos θ+(2*a)^2)) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (2*Real.pi)⁻¹ * ((1/|a^2-1/4|) * (2*Real.pi)) := by rw [hpois_int (2*a) hp]
      _ = 1 / |a^2 - 1/4| := by field_simp
  · -- case `a² > 1/4`, `p = 1/(2a)`
    have ha0 : a ≠ 0 := by nlinarith [hgt]
    have hp : |1/(2*a)| < 1 := by
      have hsq : (1/(2*a))^2 < 1^2 := by
        rw [div_pow, one_pow, mul_pow]
        rw [div_lt_one (by positivity)]
        nlinarith [hgt]
      simpa using (sq_lt_sq.mp hsq)
    have hrel : ∀ θ : ℝ, a^2+1/4-a*Real.cos θ =
        |a^2-1/4| * ((1-2*(1/(2*a))*Real.cos θ+(1/(2*a))^2)/(1-(1/(2*a))^2)) := by
      intro θ
      have h4 : (4:ℝ)*a^2 - 1 ≠ 0 := by nlinarith [hgt]
      rw [abs_of_pos (by linarith : (0:ℝ) < a^2-1/4)]
      have hb1 : 1 - (1/(2*a))^2 = (4*a^2-1)/(4*a^2) := by field_simp; ring
      have hb2 : 1 - 2*(1/(2*a))*Real.cos θ + (1/(2*a))^2 =
          (4*a^2-4*a*Real.cos θ+1)/(4*a^2) := by field_simp; ring
      rw [hb1, hb2, div_div_div_cancel_right₀ (by positivity : (4:ℝ)*a^2 ≠ 0), ← mul_div_assoc,
        eq_div_iff h4]
      ring
    have hpt : ∀ θ : ℝ, (a^2+1/4-a*Real.cos θ)⁻¹ =
        (1/|a^2-1/4|)*((1-(1/(2*a))^2)/(1-2*(1/(2*a))*Real.cos θ+(1/(2*a))^2)) := by
      intro θ
      exact inv_of_eq_mul_div _ _ _ _ (hrel θ) hq
        (one_sub_two_mul_cos_add_sq_pos (1/(2*a)) θ hp).ne' (h1mp2 (1/(2*a)) hp)
    calc (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi), (a^2+1/4-a*Real.cos θ)⁻¹
        = (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi),
            (1/|a^2-1/4|)*((1-(1/(2*a))^2)/(1-2*(1/(2*a))*Real.cos θ+(1/(2*a))^2)) := by
          congr 1
          exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
      _ = (2*Real.pi)⁻¹ * ((1/|a^2-1/4|) *
            ∫ θ in (0:ℝ)..(2*Real.pi),
              (1-(1/(2*a))^2)/(1-2*(1/(2*a))*Real.cos θ+(1/(2*a))^2)) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (2*Real.pi)⁻¹ * ((1/|a^2-1/4|) * (2*Real.pi)) := by rw [hpois_int (1/(2*a)) hp]
      _ = 1 / |a^2 - 1/4| := by field_simp

end Work.PTGeometric.RieszProj
