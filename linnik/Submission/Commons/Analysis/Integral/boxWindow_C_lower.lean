import Mathlib
import Submission.Commons.Analysis.Integral.integral_log_sq_add
import Submission.Commons.Analysis.Integral.integral_sq_mul_log_sq_add
import Submission.Commons.Analysis.Integral.Gform_lower
import Submission.Commons.Analysis.Integral.boxWin_small_beta

namespace Commons.Analysis.Integral

/-! ### Status and plan for `boxWindow_C_lower`

Target (unchanged): for `0 < β < 1`,
`-53/100 ≤ ∫_s in (-1/4)..(1/4), E(s,β)`, where `E = (13/5)h + P - M_B - M_β` with
`h = A/(A²+s²) + B/(B²+s²)`, `A = 3/2-β`, `B = 1+β`, `b = 2-β`, `c = 1-β`, `D = 2(b²+β²)`,
`P = 2c/(b²+s²) + 2c²/(b²+s²)² + 4c³/(b²+s²)³`,
`M_B = log((4b²+s²)/(2bs))·(1-s²/(4b²))`, `M_β = log((4β²+s²)/(2βs))·(1-s²/D)`.

Structure being built here:
* `integral_zero_u_log`, `integral_zero_u_sq_log`, `integral_zero_u_inv_sq_add{,_sq,_cube}`:
  the elementary improper integrals (done);
* `integral_h_term`, `integral_P_term`: closed forms of `∫₀^u h` and `∫₀^u P` (done);
* still to do: `∫₀^u M_B`, `∫₀^u M_β` (using `integral_log_sq_add` and
  `integral_sq_mul_log_sq_add` from the commons with `c = 4b²`, `√c = 2b`), which combine to
  the closed form `F(β) = ∫₀^{1/4} E(s,β) ds` for `β ≥ 1/4`;
* convexity of `F` on `[1/4,1]`: `F'' = T1'' + Pint'' + (-MBint'') + (-Mβint'')`, bounded below by
  `1.2308 - 0.97 + 0.07 - 0.17 > 0`.  The bound `Pint'' ≥ -0.97` is formalised here
  (`pint_lower`), using the rational minorant of `arctan` and the *polynomial* certificate
  `pint_mono_nonneg` (expansion in `(b-1)` with nonnegative coefficients);
  `-MBint'' ≥ 0.07` follows from the termwise bounds
  `(u³/(2b⁴))·LG + ... ≥ 0.07` with `LG = log(8b+1/(8b)) ∈ [2.09,2.65]` on `b ∈ [1,7/4]`;
  the bound for `-Mβint''` is via `(κ·arctan(u/(2β)))'' ≤ 0` (a rational certificate) and
  interval bounds on the remaining terms;
* then `F(β) ≥ F(β_j) + F'(β_j)(β-β_j)` at `β_j = 1/2, 11/20, 3/5` with explicit rational
  lower bounds for `F(β_j)` and two-sided rational bounds for `F'(β_j)`;
* the case `β ≤ 1/4` (branch switch of the majorant) is handled separately by crude estimates
  (margin ≈ 0.1 there), and the evenness of `E` halves the window to `[0,1/4]`.
-/



open MeasureTheory intervalIntegral Filter
open scoped Topology

/-! ### Elementary improper integrals used in the `boxWindow_C_lower` estimate -/

/-- `∫_0^u log s ds = u log u - u` for `0 < u`. -/
theorem integral_zero_u_log {u : ℝ} (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log s) = u * Real.log u - u := by
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) u,
      HasDerivAt (fun s : ℝ => s * Real.log s - s) (Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
      have h' : HasDerivAt (fun s : ℝ => s * Real.log s) ((1 : ℝ) * Real.log x + x * x⁻¹) x := h
      have hval : (1 : ℝ) * Real.log x + x * x⁻¹ = Real.log x + 1 := by
        rw [one_mul, mul_inv_cancel₀ hx0, add_comm]
      rwa [hval] at h'
    have h2 : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
    have h3 := h1.sub h2
    have hval2 : Real.log x + 1 - 1 = Real.log x := by ring
    rwa [hval2] at h3
  have hint : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) u := intervalIntegrable_log'
  have hlim0 : Tendsto (fun s : ℝ => s * Real.log s - s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.log s * s ^ (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    have h1' : Tendsto (fun s : ℝ => s * Real.log s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa [Real.rpow_one, mul_comm] using h1
    have h2 : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1'.sub h2
  have hlimu : Tendsto (fun s : ℝ => s * Real.log s - s) (𝓝[<] u)
      (𝓝 (u * Real.log u - u)) := by
    have hcont : ContinuousAt (fun s : ℝ => s * Real.log s - s) u := by
      apply ContinuousAt.sub
      · exact continuousAt_id.mul (Real.continuousAt_log (ne_of_gt hu))
      · exact continuousAt_id
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (b := u)
    (f := fun s : ℝ => s * Real.log s - s) (f' := fun s : ℝ => Real.log s) hu hderiv hint hlim0 hlimu

  linarith

/-- `∫_0^u s^2 log s ds = (u^3/3) log u - u^3/9` for `0 < u`. -/
theorem integral_zero_u_sq_log {u : ℝ} (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, s^2 * Real.log s) = (u^3/3) * Real.log u - u^3/9 := by
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) u,
      HasDerivAt (fun s : ℝ => (s^3/3) * Real.log s - s^3/9) (x^2 * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      norm_num at h
      exact h
    have h2 : HasDerivAt (fun s : ℝ => Real.log s) (x⁻¹) x := Real.hasDerivAt_log hx0
    have h3 := h1.mul h2
    have h4 : HasDerivAt (fun s : ℝ => s^3/9) (x^2/3) x := by
      have h := (hasDerivAt_pow 3 x).div_const (9:ℝ)
      norm_num at h
      rw [show (3:ℝ)*x^2/9 = x^2/3 by ring] at h
      exact h
    have h5 := h3.sub h4
    have hval : (x^2) * Real.log x + x^3/3 * x⁻¹ - x^2/3 = x^2 * Real.log x := by
      field_simp
      ring
    rwa [hval] at h5
  have hint : IntervalIntegrable (fun s : ℝ => s^2 * Real.log s) volume (0:ℝ) u := by
    have h : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) u := intervalIntegrable_log'
    exact h.continuousOn_mul (a := (0:ℝ)) (b := u) (continuousOn_id.pow 2)
  have hlim0 : Tendsto (fun s : ℝ => (s^3/3) * Real.log s - s^3/9) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.log s * s ^ (3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
    have h2 : Tendsto (fun s : ℝ => Real.log s * s^3) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa [Real.rpow_natCast] using h1
    have h3 : Tendsto (fun s : ℝ => s^3/3 * Real.log s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := (h2.const_mul (1/3 : ℝ))
      have h'' : Tendsto (fun s : ℝ => (1/3) * (Real.log s * s^3)) (𝓝[>] (0:ℝ)) (𝓝 ((1/3) * 0)) := h
      rw [mul_zero] at h''
      refine h''.congr' ?_
      filter_upwards with s
      ring
    have h4 : Tendsto (fun s : ℝ => s^3/9) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => s^3/9) := by continuity
      have hh := hc.continuousAt (x := (0:ℝ))
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h3.sub h4
  have hlimu : Tendsto (fun s : ℝ => (s^3/3) * Real.log s - s^3/9) (𝓝[<] u)
      (𝓝 ((u^3/3) * Real.log u - u^3/9)) := by
    have hcont : ContinuousAt (fun s : ℝ => (s^3/3) * Real.log s - s^3/9) u := by
      apply ContinuousAt.sub
      · exact ((continuousAt_id.pow 3).div_const 3).mul (Real.continuousAt_log (ne_of_gt hu))
      · exact (continuousAt_id.pow 3).div_const 9
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (b := u)
    (f := fun s : ℝ => (s^3/3) * Real.log s - s^3/9) (f' := fun s : ℝ => s^2 * Real.log s)
    hu hderiv hint hlim0 hlimu
  linarith

/-- `∫_0^u ds/(b^2+s^2) = arctan(u/b)/b` for `0 < b`. -/
theorem integral_zero_u_inv_sq_add {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, (b^2 + s^2)⁻¹) = Real.arctan (u/b) / b := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u,
      HasDerivAt (fun s : ℝ => Real.arctan (s/b) / b) ((b^2 + x^2)⁻¹) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => s/b) (1/b) x := (hasDerivAt_id x).div_const b
    have h2 : HasDerivAt (fun s : ℝ => Real.arctan (s/b)) ((1/(1+(x/b)^2)) * (1/b)) x := h1.arctan
    have h3 : HasDerivAt (fun s : ℝ => Real.arctan (s/b) / b) (((1/(1+(x/b)^2)) * (1/b)) / b) x :=
      h2.div_const b
    have hval : ((1/(1+(x/b)^2)) * (1/b)) / b = (b^2+x^2)⁻¹ := by
      rw [inv_eq_one_div]; field_simp
    rwa [hval] at h3
  have hint : IntervalIntegrable (fun s : ℝ => (b^2+s^2)⁻¹) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [mul_zero, Real.arctan_zero, zero_div, sub_zero] at h
  rw [h]

/-- `∫_0^u ds/(b^2+s^2)^2 = (arctan(u/b) + b*u/(b^2+u^2))/(2*b^3)` for `0 < b`. -/
theorem integral_zero_u_inv_sq_add_sq {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, ((b^2 + s^2)^2)⁻¹) =
      (Real.arctan (u/b) + b*u/(b^2+u^2)) / (2*b^3) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u,
      HasDerivAt (fun s : ℝ => (Real.arctan (s/b) + b*s/(b^2+s^2)) / (2*b^3))
        (((b^2 + x^2)^2)⁻¹) x := by
    intro x hx
    have hpos : 0 < b^2 + x^2 := by positivity
    have hne : b^2 + x^2 ≠ 0 := ne_of_gt hpos
    have h1 : HasDerivAt (fun s : ℝ => s/b) (1/b) x := (hasDerivAt_id x).div_const b
    have h2 : HasDerivAt (fun s : ℝ => Real.arctan (s/b)) ((1/(1+(x/b)^2)) * (1/b)) x := h1.arctan
    have hnum : HasDerivAt (fun s : ℝ => b*s) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have hden : HasDerivAt (fun s : ℝ => b^2+s^2) (2*x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (b^2))
    have h3 := hnum.div hden hne
    have h3fun : ((fun s : ℝ => b*s)/(fun s : ℝ => b^2+s^2)) = fun s : ℝ => b*s/(b^2+s^2) := by
      funext s; rfl
    rw [h3fun] at h3
    have h4 : HasDerivAt (fun s : ℝ => Real.arctan (s/b) + b*s/(b^2+s^2))
        ((1/(1+(x/b)^2)) * (1/b) + (b*(b^2+x^2) - b*x*(2*x))/(b^2+x^2)^2) x := h2.add h3
    have h5 : HasDerivAt (fun s : ℝ => (Real.arctan (s/b) + b*s/(b^2+s^2)) / (2*b^3))
        (((1/(1+(x/b)^2)) * (1/b) + (b*(b^2+x^2) - b*x*(2*x))/(b^2+x^2)^2) / (2*b^3)) x :=
      h4.div_const (2*b^3)
    have hval : ((1/(1+(x/b)^2)) * (1/b) + (b*(b^2+x^2) - b*x*(2*x))/(b^2+x^2)^2) / (2*b^3)
        = ((b^2 + x^2)^2)⁻¹ := by
      rw [inv_eq_one_div]; field_simp; ring
    rwa [hval] at h5
  have hint : IntervalIntegrable (fun s : ℝ => ((b^2+s^2)^2)⁻¹) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [mul_zero, Real.arctan_zero, zero_div, zero_add, sub_zero] at h
  rw [h]

/-- `∫_0^u ds/(b^2+s^2)^3 = 3·arctan(u/b)/(8b^5) + u(5b^2+3u^2)/(8b^4(b^2+u^2)^2)` for `0 < b`. -/
theorem integral_zero_u_inv_sq_add_cube {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, ((b^2 + s^2)^3)⁻¹) =
      3*Real.arctan (u/b)/(8*b^5) + u*(5*b^2+3*u^2)/(8*b^4*(b^2+u^2)^2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u,
      HasDerivAt (fun s : ℝ => 3*Real.arctan (s/b)/(8*b^5) + s*(5*b^2+3*s^2)/(8*b^4*(b^2+s^2)^2))
        (((b^2 + x^2)^3)⁻¹) x := by
    intro x hx
    have hpos : 0 < b^2 + x^2 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => s/b) (1/b) x := (hasDerivAt_id x).div_const b
    have h2 := h1.arctan
    have hA : HasDerivAt (fun s : ℝ => 3*Real.arctan (s/b)/(8*b^5))
        (3 * ((1/(1+(x/b)^2)) * (1/b)) / (8*b^5)) x := (h2.const_mul 3).div_const (8*b^5)
    have hq : HasDerivAt (fun s : ℝ => 5*b^2 + 3*s^2) (6*x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul 3
      have h' := h.const_add (5*b^2)
      exact h'.congr_deriv (by norm_num <;> ring)
    have hn := (hasDerivAt_id x).mul hq
    have hnum2 : HasDerivAt (fun s : ℝ => s*(5*b^2+3*s^2)) (5*b^2 + 9*x^2) x :=
      hn.congr_deriv (by simp only [id_eq, one_mul]; ring)
    have hinner : HasDerivAt (fun s : ℝ => b^2+s^2) (2*x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (b^2))
    have hden : HasDerivAt (fun s : ℝ => 8*b^4*(b^2+s^2)^2) (8*b^4*(4*x*(b^2+x^2))) x := by
      have hp := hinner.pow 2
      have hsq : ((fun s : ℝ => b^2+s^2)^2) = fun s : ℝ => (b^2+s^2)^2 := rfl
      rw [hsq] at hp
      have hp' : HasDerivAt (fun s : ℝ => (b^2+s^2)^2) (4*x*(b^2+x^2)) x :=
        hp.congr_deriv (by norm_num <;> ring)
      exact (hp'.const_mul (8*b^4)).congr_deriv (by ring)
    have hB : HasDerivAt (fun s : ℝ => s*(5*b^2+3*s^2)/(8*b^4*(b^2+s^2)^2))
        (((5*b^2+9*x^2)*(b^2+x^2) - 4*x^2*(5*b^2+3*x^2))/(8*b^4*(b^2+x^2)^3)) x :=
      (hnum2.div hden (by positivity)).congr_deriv (by field_simp <;> ring)
    have hsum := hA.add hB
    exact hsum.congr_deriv (by rw [inv_eq_one_div]; field_simp <;> ring)
  have hint : IntervalIntegrable (fun s : ℝ => ((b^2+s^2)^3)⁻¹) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [mul_zero, Real.arctan_zero, zero_div, zero_add, sub_zero] at h
  rw [h]; ring

/-- `∫_0^u (A/(A^2+s^2) + B/(B^2+s^2)) ds = arctan(u/A) + arctan(u/B)`. -/
theorem integral_h_term {A B u : ℝ} (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, A/(A^2+s^2) + B/(B^2+s^2))
      = Real.arctan (u/A) + Real.arctan (u/B) := by
  have h1 : (∫ s in (0:ℝ)..u, A/(A^2+s^2)) = Real.arctan (u/A) := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u, HasDerivAt (fun s : ℝ => Real.arctan (s/A)) (A/(A^2+x^2)) x := by
      intro x hx
      have h1 : HasDerivAt (fun s : ℝ => s/A) (1/A) x := (hasDerivAt_id x).div_const A
      have h2 := h1.arctan
      exact h2.congr_deriv (by field_simp <;> ring)
    have hint : IntervalIntegrable (fun s : ℝ => A/(A^2+s^2)) volume (0:ℝ) u := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; positivity
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [zero_div, Real.arctan_zero, sub_zero] at h
    rw [h]
  have h2 : (∫ s in (0:ℝ)..u, B/(B^2+s^2)) = Real.arctan (u/B) := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u, HasDerivAt (fun s : ℝ => Real.arctan (s/B)) (B/(B^2+x^2)) x := by
      intro x hx
      have h1 : HasDerivAt (fun s : ℝ => s/B) (1/B) x := (hasDerivAt_id x).div_const B
      have h2 := h1.arctan
      exact h2.congr_deriv (by field_simp <;> ring)
    have hint : IntervalIntegrable (fun s : ℝ => B/(B^2+s^2)) volume (0:ℝ) u := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; positivity
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [zero_div, Real.arctan_zero, sub_zero] at h
    rw [h]
  have hi1 : IntervalIntegrable (fun s : ℝ => A/(A^2+s^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; positivity
  have hi2 : IntervalIntegrable (fun s : ℝ => B/(B^2+s^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; positivity
  rw [intervalIntegral.integral_add hi1 hi2, h1, h2]

/-- The `P`-piece integral:
`∫_0^u (2c/(b^2+s^2) + 2c^2/(b^2+s^2)^2 + 4c^3/(b^2+s^2)^3) ds`
`= (2c/b + c^2/b^3 + 3c^3/(2b^5)) arctan(u/b) + c^2 u/(b^2(b^2+u^2)) + c^3 u (5b^2+3u^2)/(2b^4(b^2+u^2)^2)`. -/
theorem integral_P_term {b c u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, 2*c/(b^2+s^2) + 2*c^2/((b^2+s^2)^2) + 4*c^3/((b^2+s^2)^3))
      = (2*c/b + c^2/b^3 + 3*c^3/(2*b^5))*Real.arctan (u/b)
        + c^2*u/(b^2*(b^2+u^2)) + c^3*u*(5*b^2+3*u^2)/(2*b^4*(b^2+u^2)^2) := by
  have hi1 : IntervalIntegrable (fun s : ℝ => 2*c/(b^2+s^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; positivity
  have hi2 : IntervalIntegrable (fun s : ℝ => 2*c^2/((b^2+s^2)^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; positivity
  have hi3 : IntervalIntegrable (fun s : ℝ => 4*c^3/((b^2+s^2)^3)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; positivity
  have e1 : (∫ s in (0:ℝ)..u, 2*c/(b^2+s^2)) = 2*c*(Real.arctan (u/b)/b) := by
    have h : (∫ s in (0:ℝ)..u, (2*c) * ((b^2+s^2)⁻¹)) = (2*c) * (Real.arctan (u/b) * b⁻¹) := by
      rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add hb hu]
      ring
    simpa only [div_eq_mul_inv] using h
  have e2 : (∫ s in (0:ℝ)..u, 2*c^2/((b^2+s^2)^2))
      = 2*c^2*((Real.arctan (u/b) + b*u/(b^2+u^2)) / (2*b^3)) := by
    have h : (∫ s in (0:ℝ)..u, (2*c^2) * (((b^2+s^2)^2)⁻¹))
        = (2*c^2) * ((Real.arctan (u/b) + b*u/(b^2+u^2)) * (2*b^3)⁻¹) := by
      rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add_sq hb hu]
      ring
    simpa only [div_eq_mul_inv] using h
  have e3 : (∫ s in (0:ℝ)..u, 4*c^3/((b^2+s^2)^3))
      = 4*c^3*(3*Real.arctan (u/b)/(8*b^5) + u*(5*b^2+3*u^2)/(8*b^4*(b^2+u^2)^2)) := by
    have h : (∫ s in (0:ℝ)..u, (4*c^3) * (((b^2+s^2)^3)⁻¹))
        = (4*c^3) * (3*Real.arctan (u/b) * (8*b^5)⁻¹
            + u*(5*b^2+3*u^2) * (8*b^4*(b^2+u^2)^2)⁻¹) := by
      rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add_cube hb hu]
      ring
    simpa only [div_eq_mul_inv] using h
  have hsum1 : IntervalIntegrable (fun s : ℝ => 2*c/(b^2+s^2) + 2*c^2/((b^2+s^2)^2)) volume (0:ℝ) u :=
    hi1.add hi2
  have hsum2 : IntervalIntegrable
      (fun s : ℝ => 2*c/(b^2+s^2) + 2*c^2/((b^2+s^2)^2) + 4*c^3/((b^2+s^2)^3)) volume (0:ℝ) u :=
    hsum1.add hi3
  rw [intervalIntegral.integral_add hsum1 hi3, intervalIntegral.integral_add hi1 hi2, e1, e2, e3]
  field_simp
  ring


noncomputable def rr2 (b : ℝ) : ℝ :=
  (98304*b^10+98304*b^9-2125824*b^8+3664896*b^7-1844352*b^6+319232*b^5-177408*b^4+13628*b^3-7572*b^2+216*b-120)/(65536*b^14+16384*b^12+1536*b^10+64*b^8+b^6)

noncomputable def kk (b : ℝ) : ℝ := 2*(b-1)/b + (b-1)^2/b^3 + 3*(b-1)^3/(2*b^5)

noncomputable def kk1 (b : ℝ) : ℝ := (b^4+b^3+(21/2)*b^2-18*b+15/2)/b^6

noncomputable def kk2 (b : ℝ) : ℝ := (-2*b^4-3*b^3-42*b^2+90*b-45)/b^7

lemma pint_poly_expanded {b : ℝ} (hb : 1 ≤ b) :
    (0:ℝ) ≤ (78114717696)*(b-1)^22 + (1718523789312)*(b-1)^21 + (18073792806912)*(b-1)^20 + (120963056271360)*(b-1)^19 + (578509492715520)*(b-1)^18 + (2104340275789824)*(b-1)^17 + (6045331910033408)*(b-1)^16 + (14037277504176128)*(b-1)^15 + (26696753135800320)*(b-1)^14 + (41831809573150720)*(b-1)^13 + (54016503343923712)*(b-1)^12 + (57230380696295424)*(b-1)^11 + (49332033386251824)*(b-1)^10 + (34157803616579040)*(b-1)^9 + (18662118505899120)*(b-1)^8 + (7855290948768896)*(b-1)^7 + (2474601870410432)*(b-1)^6 + (571561931229072)*(b-1)^5 + (102105657548130)*(b-1)^4 + (17866727456595)*(b-1)^3 + (3247354448487)*(b-1)^2 + (344849773379)*(b-1) + (1138725314) := by
  positivity

lemma pint_mono_nonneg {b : ℝ} (hb : 1 ≤ b) :
    (0:ℝ) ≤ (1125) + (-2250)*b + (55050)*b^2 + (-107925)*b^3 + (-1677550)*b^4 + (3459600)*b^5 + (-195146400)*b^6 + (386956800)*b^7 + (-6418099200)*b^8 + (12461875200)*b^9 + (-108900756944)*b^10 + (207604531200)*b^11 + (-1004872871424)*b^12 + (1864158412800)*b^13 + (-4332121436160)*b^14 + (7199313100800)*b^15 + (-4042927636480)*b^16 + (20132659200)*b^17 + (4577034240)*b^18 + (80530636800)*b^19 + (29293019136)*b^20 + (78114717696)*b^22 := by
  have hexp : ((1125) + (-2250)*b + (55050)*b^2 + (-107925)*b^3 + (-1677550)*b^4 + (3459600)*b^5 + (-195146400)*b^6 + (386956800)*b^7 + (-6418099200)*b^8 + (12461875200)*b^9 + (-108900756944)*b^10 + (207604531200)*b^11 + (-1004872871424)*b^12 + (1864158412800)*b^13 + (-4332121436160)*b^14 + (7199313100800)*b^15 + (-4042927636480)*b^16 + (20132659200)*b^17 + (4577034240)*b^18 + (80530636800)*b^19 + (29293019136)*b^20 + (78114717696)*b^22 : ℝ) = (78114717696)*(b-1)^22 + (1718523789312)*(b-1)^21 + (18073792806912)*(b-1)^20 + (120963056271360)*(b-1)^19 + (578509492715520)*(b-1)^18 + (2104340275789824)*(b-1)^17 + (6045331910033408)*(b-1)^16 + (14037277504176128)*(b-1)^15 + (26696753135800320)*(b-1)^14 + (41831809573150720)*(b-1)^13 + (54016503343923712)*(b-1)^12 + (57230380696295424)*(b-1)^11 + (49332033386251824)*(b-1)^10 + (34157803616579040)*(b-1)^9 + (18662118505899120)*(b-1)^8 + (7855290948768896)*(b-1)^7 + (2474601870410432)*(b-1)^6 + (571561931229072)*(b-1)^5 + (102105657548130)*(b-1)^4 + (17866727456595)*(b-1)^3 + (3247354448487)*(b-1)^2 + (344849773379)*(b-1) + (1138725314) := by ring
  rw [hexp]
  positivity

lemma pint_lower {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 7/4) :
    (0:ℝ) ≤ (97/100) + kk2 b * ((1/4)/b - ((1/4)/b)^3/3) - 2*(kk1 b)*(1/4)/(b^2+(1/4)^2)
      + (kk b)*2*b*(1/4)/(b^2+(1/4)^2)^2 + rr2 b := by
  have hD : (0:ℝ) < 4800*b^10*(16*b^2+1)^6 := by positivity
  have hnum : (0:ℝ) ≤ (1125) + (-2250)*b + (55050)*b^2 + (-107925)*b^3 + (-1677550)*b^4 + (3459600)*b^5 + (-195146400)*b^6 + (386956800)*b^7 + (-6418099200)*b^8 + (12461875200)*b^9 + (-108900756944)*b^10 + (207604531200)*b^11 + (-1004872871424)*b^12 + (1864158412800)*b^13 + (-4332121436160)*b^14 + (7199313100800)*b^15 + (-4042927636480)*b^16 + (20132659200)*b^17 + (4577034240)*b^18 + (80530636800)*b^19 + (29293019136)*b^20 + (78114717696)*b^22 := pint_mono_nonneg hb1
  have hkey : (97/100) + kk2 b * ((1/4)/b - ((1/4)/b)^3/3) - 2*(kk1 b)*(1/4)/(b^2+(1/4)^2)
      + (kk b)*2*b*(1/4)/(b^2+(1/4)^2)^2 + rr2 b
      = ((1125) + (-2250)*b + (55050)*b^2 + (-107925)*b^3 + (-1677550)*b^4 + (3459600)*b^5 + (-195146400)*b^6 + (386956800)*b^7 + (-6418099200)*b^8 + (12461875200)*b^9 + (-108900756944)*b^10 + (207604531200)*b^11 + (-1004872871424)*b^12 + (1864158412800)*b^13 + (-4332121436160)*b^14 + (7199313100800)*b^15 + (-4042927636480)*b^16 + (20132659200)*b^17 + (4577034240)*b^18 + (80530636800)*b^19 + (29293019136)*b^20 + (78114717696)*b^22)/(4800*b^10*(16*b^2+1)^6) := by
    unfold rr2 kk kk1 kk2
    field_simp
    ring
  rw [hkey]
  exact div_nonneg hnum hD.le



/-- `∫_0^u (1 - s^2/D) ds = u - u^3/(3D)`. -/
theorem integral_one_sub_sq_div {D u : ℝ} (hD : D ≠ 0) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, (1 - s^2/D)) = u - u^3/(3*D) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) u,
      HasDerivAt (fun s : ℝ => s - s^3/(3*D)) (1 - x^2/D) x := by
    intro x hx
    have hp : HasDerivAt (fun s : ℝ => s^3/(3*D)) (3*x^2/(3*D)) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3*D)
      simpa using h
    have h := (hasDerivAt_id x).sub hp
    exact h.congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun s : ℝ => 1 - s^2/D) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [zero_pow (by norm_num : (3:ℕ) ≠ 0), div_zero, sub_zero] at h
  rw [h]
  field_simp
  ring

/-- `∫_0^u log(c+s^2)·(1-s^2/D) ds` in closed form. -/
theorem integral_log_sq_add_mul {c D u : ℝ} (hc : 0 < c) (hD : D ≠ 0) (hu : 0 ≤ u) :
    (∫ s in (0:ℝ)..u, Real.log (c+s^2) * (1 - s^2/D))
      = (u - u^3/(3*D))*Real.log (c+u^2)
        + (2*Real.sqrt c + 2*(c*Real.sqrt c)/(3*D))*Real.arctan (u/Real.sqrt c)
        - 2*u + (2*u^3/9 - 2*c*u/3)/D := by
  have hA : (∫ s in (0:ℝ)..u, Real.log (c+s^2))
      = u*Real.log (c+u^2) - 2*u + 2*Real.sqrt c*Real.arctan (u/Real.sqrt c) := by
    have h := Commons.Analysis.Integral.integral_log_sq_add (c := c) (p := 0) (q := u) hc
    simpa using h
  have hB : (∫ s in (0:ℝ)..u, s^2*Real.log (c+s^2))
      = (u^3/3)*Real.log (c+u^2)
        - (2/3)*(u^3/3 - c*u + c*Real.sqrt c*Real.arctan (u/Real.sqrt c)) := by
    have h := Commons.Analysis.Integral.integral_sq_mul_log_sq_add (c := c) (p := 0) (q := u) hc
    simpa using h
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.log (c+s^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.log (by fun_prop) (fun x hx => by positivity)
  have hi2 : IntervalIntegrable (fun s : ℝ => s^2*Real.log (c+s^2)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul (by fun_prop)
      (ContinuousOn.log (by fun_prop) (fun x hx => by positivity))
  have e : (∫ s in (0:ℝ)..u, Real.log (c+s^2) * (1 - s^2/D))
      = (∫ s in (0:ℝ)..u, Real.log (c+s^2))
        - (1/D)*(∫ s in (0:ℝ)..u, s^2*Real.log (c+s^2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 (hi2.const_mul _)]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [e, hA, hB]
  field_simp
  ring

/-- `∫_0^u log s · (1 - s^2/D) ds` in closed form. -/
theorem integral_log_mul_one_sub_sq_div {D u : ℝ} (hD : D ≠ 0) (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log s * (1 - s^2/D))
      = (u*Real.log u - u) - (1/D)*((u^3/3)*Real.log u - u^3/9) := by
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) u := intervalIntegrable_log'
  have hi2 : IntervalIntegrable (fun s : ℝ => s^2*Real.log s) volume (0:ℝ) u :=
    hi1.continuousOn_mul (a := (0:ℝ)) (b := u) (continuousOn_id.pow 2)
  have e : (∫ s in (0:ℝ)..u, Real.log s * (1 - s^2/D))
      = (∫ s in (0:ℝ)..u, Real.log s) - (1/D)*(∫ s in (0:ℝ)..u, s^2*Real.log s) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 (hi2.const_mul _)]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [e, integral_zero_u_log hu, integral_zero_u_sq_log hu]

/-- `∫_0^u log((a^2+s^2)/(a s))·(1-s^2/D) ds` in closed form. -/
theorem integral_log_ratio_mul {a D u : ℝ} (ha : 0 < a) (hD : 0 < D) (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log ((a^2+s^2)/(a*s)) * (1 - s^2/D))
      = (u - u^3/(3*D)) * Real.log ((a^2+u^2)/(a*u))
        + (2*a + 2*a^3/(3*D))*Real.arctan (u/a) - u + (u^3/9 - 2*a^2*u/3)/D := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hs2 : Real.sqrt (a^2) = a := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hc : (0:ℝ) < a^2 := by positivity
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0:ℝ) u →
      Real.log ((a^2+s^2)/(a*s)) * (1 - s^2/D)
        = (Real.log (a^2+s^2) - Real.log a - Real.log s) * (1 - s^2/D) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_contra h0
    apply hs
    intro hmem
    have hsne : s ≠ 0 := fun h => h0 (by simpa [h])
    have h2 : a*s ≠ 0 := mul_ne_zero ha0 hsne
    have h4 : a^2+s^2 ≠ 0 := by positivity
    rw [Real.log_div h4 h2, Real.log_mul ha0 hsne]
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hA : (∫ s in (0:ℝ)..u, Real.log (a^2+s^2) * (1 - s^2/D))
      = (u - u^3/(3*D))*Real.log (a^2+u^2)
        + (2*Real.sqrt (a^2) + 2*((a^2)*Real.sqrt (a^2))/(3*D))*Real.arctan (u/Real.sqrt (a^2))
        - 2*u + (2*u^3/9 - 2*(a^2)*u/3)/D := integral_log_sq_add_mul hc hD0 hu.le
  have hC : (∫ s in (0:ℝ)..u, Real.log a * (1 - s^2/D)) = Real.log a * (u - u^3/(3*D)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact integral_one_sub_sq_div hD0 hu.le
  have hE : (∫ s in (0:ℝ)..u, Real.log s * (1 - s^2/D))
      = (u*Real.log u - u) - (1/D)*((u^3/3)*Real.log u - u^3/9) :=
    integral_log_mul_one_sub_sq_div hD0 hu
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.log (a^2+s^2) * (1 - s^2/D)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul (ContinuousOn.log (by fun_prop) (fun x hx => by positivity)) (by fun_prop)
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log a * (1 - s^2/D)) volume (0:ℝ) u := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.mul continuousOn_const (by fun_prop)
  have hi3 : IntervalIntegrable (fun s : ℝ => Real.log s * (1 - s^2/D)) volume (0:ℝ) u := by
    have h : IntervalIntegrable (fun x : ℝ => (1 - x^2/D) * Real.log x) volume (0:ℝ) u :=
      intervalIntegrable_log'.continuousOn_mul (a := (0:ℝ)) (b := u)
        (g := fun s : ℝ => 1 - s^2/D)
        (continuousOn_const.sub ((continuousOn_id.pow 2).div_const D))
    simpa [mul_comm] using h
  have hfuneq : (fun s : ℝ => (Real.log (a^2+s^2) - Real.log a - Real.log s) * (1 - s^2/D))
      = fun s : ℝ => (Real.log (a^2+s^2) * (1 - s^2/D) - Real.log a * (1 - s^2/D))
          - Real.log s * (1 - s^2/D) := by
    funext s; ring
  have hsum : (∫ s in (0:ℝ)..u, (Real.log (a^2+s^2) - Real.log a - Real.log s) * (1 - s^2/D))
      = (∫ s in (0:ℝ)..u, Real.log (a^2+s^2) * (1 - s^2/D))
        - (∫ s in (0:ℝ)..u, Real.log a * (1 - s^2/D))
        - (∫ s in (0:ℝ)..u, Real.log s * (1 - s^2/D)) := by
    rw [hfuneq, intervalIntegral.integral_sub (hi1.sub hi2) hi3,
      intervalIntegral.integral_sub hi1 hi2]
  rw [hsum, hA, hC, hE, hs2]
  rw [Real.log_div (by positivity : a^2+u^2 ≠ 0) (mul_ne_zero ha0 hu0)]
  rw [Real.log_mul ha0 hu0]
  field_simp
  ring

/-- `∫_0^u log((4b^2+s^2)/(2bs))·(1-s^2/(4b^2)) ds` in closed form. -/
theorem integral_MB_term {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log ((4*b^2+s^2)/(2*b*s)) * (1 - s^2/(4*b^2)))
      = (u - u^3/(12*b^2)) * Real.log ((4*b^2+u^2)/(2*b*u))
        + (16*b/3)*Real.arctan (u/(2*b)) - 5*u/3 + u^3/(36*b^2) := by
  have h := integral_log_ratio_mul (a := 2*b) (D := 4*b^2) (u := u) (by positivity) (by positivity) hu
  rw [show (2*b)^2 = 4*b^2 by ring] at h
  have hlog : ((4*b^2)+u^2)/((2*b)*u) = (4*b^2+u^2)/(2*b*u) := by ring
  rw [hlog] at h
  rw [h]
  field_simp
  ring

/-- `∫_0^u log((4β^2+s^2)/(2βs))·(1-s^2/D) ds` with `D = 2(b^2+β^2)`, in closed form. -/
theorem integral_Mbeta_term {b β u : ℝ} (hb : 0 < b) (hβ : 0 < β) (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log ((4*β^2+s^2)/(2*β*s)) * (1 - s^2/(2*(b^2+β^2))))
      = (u - u^3/(3*(2*(b^2+β^2)))) * Real.log ((4*β^2+u^2)/(2*β*u))
        + (4*β + 16*β^3/(3*(2*(b^2+β^2))))*Real.arctan (u/(2*β))
        - u + (u^3/9 - 8*β^2*u/3)/(2*(b^2+β^2)) := by
  have h := integral_log_ratio_mul (a := 2*β) (D := 2*(b^2+β^2)) (u := u)
    (by positivity) (by positivity) hu
  rw [show (2*β)^2 = 4*β^2 by ring] at h
  have hlog : ((4*β^2)+u^2)/((2*β)*u) = (4*β^2+u^2)/(2*β*u) := by ring
  rw [hlog] at h
  rw [h]
  field_simp
  ring
/-- The integrand of the target statement (verbatim). -/
noncomputable def Win (β s : ℝ) : ℝ :=
  ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
    - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
         else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
    - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
         else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )

/-- The closed form of `∫_0^{1/4} Win β s` for `β ∈ [1/4,1]`. -/
noncomputable def Gform (β : ℝ) : ℝ :=
  (13/5)*(Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)))
  + ( (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
      + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
      + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) )
  - ( (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log ((4*(2-β)^2+(1/4)^2)/(2*(2-β)*(1/4)))
      + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) )
  - ( (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log ((4*β^2+(1/4)^2)/(2*β*(1/4)))
      + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
      + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) )

/-- `Win` is even in `s`. -/
lemma Win_neg (β s : ℝ) : Win β (-s) = Win β s := by
  unfold Win
  simp only [abs_neg, neg_sq]

/-- On `(0,1/4]` with `β ∈ [1/4,1]` both `if`s take their *then*-branch and `|s| = s`. -/
lemma Win_eq_explicit {β s : ℝ} (hβ1 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    Win β s
      = (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
        - Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2))) := by
  unfold Win
  have hsabs : |s| = s := abs_of_pos hs0
  have h2b : (2:ℝ)-β ≥ 1 := by linarith
  have hif1 : (|s|:ℝ) ≤ 2-β := by rw [hsabs]; linarith
  have hif2 : (|s|:ℝ) ≤ β := by rw [hsabs]; linarith
  rw [if_pos hif1, if_pos hif2, hsabs]

/-- The `h`-summand of the integrand. -/
noncomputable def WinH (β : ℝ) : ℝ → ℝ :=
  fun s => (3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)

/-- The `P`-summand of the integrand in the `(2-β)²-β²` form. -/
noncomputable def WinP (β : ℝ) : ℝ → ℝ :=
  fun s => ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)

/-- The `P`-summand in the `2c/(b²+s²)` form (`c = 1-β`, `b = 2-β`). -/
noncomputable def WinPint (β : ℝ) : ℝ → ℝ :=
  fun s => 2*(1-β)/((2-β)^2+s^2) + 2*(1-β)^2/(((2-β)^2+s^2)^2)
    + 4*(1-β)^3/(((2-β)^2+s^2)^3)

/-- The `B`-majorant summand. -/
noncomputable def WinMB (β : ℝ) : ℝ → ℝ :=
  fun s => Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))

/-- The `β`-majorant summand. -/
noncomputable def WinMb (β : ℝ) : ℝ → ℝ :=
  fun s => Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))

lemma WinH_cont (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : Continuous (WinH β) := by
  have hb : (0:ℝ) < 2-β := by linarith
  unfold WinH
  apply Continuous.add
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have : (0:ℝ) < (3/2-β)^2+x^2 := by nlinarith [sq_nonneg x, sq_nonneg (3/2-β-1), h2]
    linarith
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have : (0:ℝ) < (1+β)^2+x^2 := by nlinarith [sq_nonneg x, sq_nonneg β, h1]
    linarith

lemma WinP_cont (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : Continuous (WinP β) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hpos : ∀ x : ℝ, (0:ℝ) < (2-β)^2+x^2 := fun x =>
    by nlinarith [sq_nonneg x, sq_nonneg (2-β-1), hb]
  unfold WinP
  apply Continuous.add
  apply Continuous.add
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity

lemma WinPint_cont (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : Continuous (WinPint β) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hpos : ∀ x : ℝ, (0:ℝ) < (2-β)^2+x^2 := fun x =>
    by nlinarith [sq_nonneg x, sq_nonneg (2-β-1), hb]
  unfold WinPint
  apply Continuous.add
  apply Continuous.add
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity
  · apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : (0:ℝ) < (2-β)^2+x^2 := hpos x
    positivity

lemma WinP_eq_WinPint (β : ℝ) (h2 : β ≤ 1) : WinP β = WinPint β := by
  unfold WinP WinPint
  funext s
  have hb : (0:ℝ) < 2-β := by linarith
  have hD : ((2-β)^2+s^2) ≠ 0 := by
    have h : (0:ℝ) < (2-β)^2+s^2 := by nlinarith [sq_nonneg s, sq_nonneg (2-β-1), hb]
    linarith
  have h4 : (2-β)^2-β^2 = 4*(1-β) := by ring
  rw [h4]
  field_simp
  ring

lemma WinMB_int (β : ℝ) (h2 : β ≤ 1) :
    IntervalIntegrable (WinMB β) volume (0:ℝ) (1/4) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hb0 : (0:ℝ) < 2*(2-β) := by linarith
  unfold WinMB
  have hbase : IntervalIntegrable (fun s : ℝ => Real.log (4*(2-β)^2+s^2)*(1-s^2/(4*(2-β)^2))
      - Real.log (2*(2-β))*(1-s^2/(4*(2-β)^2)) - Real.log s*(1-s^2/(4*(2-β)^2))) volume (0:ℝ) (1/4) := by
    apply IntervalIntegrable.sub
    · apply IntervalIntegrable.sub
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul (ContinuousOn.log (by fun_prop) (fun x hx => by positivity)) (by fun_prop)
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul continuousOn_const (by fun_prop)
    · have := intervalIntegrable_log'.continuousOn_mul (a := (0:ℝ)) (b := (1/4:ℝ))
        (g := fun s : ℝ => 1-s^2/(4*(2-β)^2))
        (continuousOn_const.sub ((continuousOn_id.pow 2).div_const _))
      simpa [mul_comm] using this
  refine hbase.congr ?_
  intro s hs
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hs
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have h4 : (4*(2-β)^2+s^2) ≠ 0 := by positivity
  have h5 : (2*(2-β)*s) ≠ 0 := mul_ne_zero (ne_of_gt hb0) hs0
  simp only []
  rw [Real.log_div h4 h5, Real.log_mul (ne_of_gt hb0) hs0]
  ring

lemma WinMb_int (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) :
    IntervalIntegrable (WinMb β) volume (0:ℝ) (1/4) := by
  have hbeta : (0:ℝ) < β := by linarith
  have hb0 : (0:ℝ) < 2*β := by linarith
  unfold WinMb
  have hbase : IntervalIntegrable (fun s : ℝ => Real.log (4*β^2+s^2)*(1-s^2/(2*((2-β)^2+β^2)))
      - Real.log (2*β)*(1-s^2/(2*((2-β)^2+β^2))) - Real.log s*(1-s^2/(2*((2-β)^2+β^2)))) volume (0:ℝ) (1/4) := by
    apply IntervalIntegrable.sub
    · apply IntervalIntegrable.sub
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul (ContinuousOn.log (by fun_prop) (fun x hx => by positivity)) (by fun_prop)
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.mul continuousOn_const (by fun_prop)
    · have := intervalIntegrable_log'.continuousOn_mul (a := (0:ℝ)) (b := (1/4:ℝ))
        (g := fun s : ℝ => 1-s^2/(2*((2-β)^2+β^2)))
        (continuousOn_const.sub ((continuousOn_id.pow 2).div_const _))
      simpa [mul_comm] using this
  refine hbase.congr ?_
  intro s hs
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hs
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have h4 : (4*β^2+s^2) ≠ 0 := by positivity
  have h5 : (2*β*s) ≠ 0 := mul_ne_zero (ne_of_gt hb0) hs0
  simp only []
  rw [Real.log_div h4 h5, Real.log_mul (ne_of_gt hb0) hs0]
  ring

/-- For `β ∈ [1/4,1]` the half-integral `∫_0^{1/4} Win β s` equals the closed form `Gform β`. -/
theorem integral_Win {β : ℝ} (hβ1 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1) :
    (∫ s in (0:ℝ)..(1/4), Win β s) = Gform β := by
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0:ℝ) (1/4) →
      Win β s = (13/5)*WinH β s + WinP β s - WinMB β s - WinMb β s := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_contra h0
    apply hs
    intro hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hmem
    rw [Win_eq_explicit hβ1 hβ2 hmem.1 hmem.2]
    unfold WinH WinP WinMB WinMb
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hF1 : IntervalIntegrable (fun s : ℝ => (13/5)*WinH β s) volume (0:ℝ) (1/4) :=
    ((WinH_cont β hβ1 hβ2).intervalIntegrable (0:ℝ) (1/4)).const_mul (13/5)
  have hF2 : IntervalIntegrable (WinP β) volume (0:ℝ) (1/4) :=
    (WinP_cont β hβ1 hβ2).intervalIntegrable (0:ℝ) (1/4)
  have hF3 : IntervalIntegrable (WinMB β) volume (0:ℝ) (1/4) := WinMB_int β hβ2
  have hF4 : IntervalIntegrable (WinMb β) volume (0:ℝ) (1/4) := WinMb_int β hβ1
  have hsplit : (∫ s in (0:ℝ)..(1/4), ((13/5)*WinH β s + WinP β s - WinMB β s - WinMb β s))
      = (13/5)*(∫ s in (0:ℝ)..(1/4), WinH β s)
        + (∫ s in (0:ℝ)..(1/4), WinP β s)
        - (∫ s in (0:ℝ)..(1/4), WinMB β s)
        - (∫ s in (0:ℝ)..(1/4), WinMb β s) := by
    have hiB : IntervalIntegrable (fun s : ℝ => (13/5)*WinH β s + WinP β s) volume (0:ℝ) (1/4) := hF1.add hF2
    have hiC : IntervalIntegrable (fun s : ℝ => (13/5)*WinH β s + WinP β s - WinMB β s) volume (0:ℝ) (1/4) :=
      hiB.sub hF3
    rw [intervalIntegral.integral_sub hiC hF4, intervalIntegral.integral_sub hiB hF3,
      intervalIntegral.integral_add hF1 hF2, intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hPeq : (∫ s in (0:ℝ)..(1/4), WinP β s) = (∫ s in (0:ℝ)..(1/4), WinPint β s) := by
    rw [show WinP β = WinPint β from WinP_eq_WinPint β hβ2]
  rw [hPeq]
  have eH : (∫ s in (0:ℝ)..(1/4), WinH β s)
      = Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)) := by
    have h := integral_h_term (A := 3/2-β) (B := 1+β) (u := 1/4) (by linarith) (by linarith) (by norm_num)
    simpa [WinH] using h
  have eQ : (∫ s in (0:ℝ)..(1/4), WinPint β s)
      = (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
        + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
        + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) := by
    have h := integral_P_term (b := 2-β) (c := 1-β) (u := 1/4) (by linarith) (by norm_num : (0:ℝ) ≤ 1/4)
    simpa [WinPint] using h
  have eMB : (∫ s in (0:ℝ)..(1/4), WinMB β s)
      = (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log ((4*(2-β)^2+(1/4)^2)/(2*(2-β)*(1/4)))
        + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) := by
    have h := integral_MB_term (b := 2-β) (u := 1/4) (by linarith) (by norm_num)
    simpa [WinMB] using h
  have eMb : (∫ s in (0:ℝ)..(1/4), WinMb β s)
      = (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log ((4*β^2+(1/4)^2)/(2*β*(1/4)))
        + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
        + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) := by
    have h := integral_Mbeta_term (b := 2-β) (β := β) (u := 1/4) (by linarith) (by linarith) (by norm_num)
    simpa [WinMb] using h
  rw [eH, eQ, eMB, eMb]
  unfold Gform
  ring
/-- `Win β` is interval-integrable on `[0,1/4]` for `β ∈ [1/4,1]`. -/
lemma Win_int_right {β : ℝ} (hβ1 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1) :
    IntervalIntegrable (Win β) volume (0:ℝ) (1/4) := by
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0:ℝ) (1/4) →
      Win β s = (13/5)*WinH β s + WinP β s - WinMB β s - WinMb β s := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_contra h0
    apply hs
    intro hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hmem
    rw [Win_eq_explicit hβ1 hβ2 hmem.1 hmem.2]
    unfold WinH WinP WinMB WinMb
    ring
  have h1 : IntervalIntegrable (fun s : ℝ => (13/5)*WinH β s) volume (0:ℝ) (1/4) :=
    ((WinH_cont β hβ1 hβ2).intervalIntegrable (0:ℝ) (1/4)).const_mul (13/5)
  have h2 : IntervalIntegrable (WinP β) volume (0:ℝ) (1/4) :=
    (WinP_cont β hβ1 hβ2).intervalIntegrable (0:ℝ) (1/4)
  have h3 : IntervalIntegrable (WinMB β) volume (0:ℝ) (1/4) := WinMB_int β hβ2
  have h4 : IntervalIntegrable (WinMb β) volume (0:ℝ) (1/4) := WinMb_int β hβ1
  have hsum : IntervalIntegrable (fun s : ℝ => (13/5)*WinH β s + WinP β s - WinMB β s - WinMb β s)
      volume (0:ℝ) (1/4) := ((h1.add h2).sub h3).sub h4
  refine hsum.congr_ae ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hae] with s hs
  intro hmem
  exact (hs hmem).symm

/-- The target integral over `[-1/4,1/4]` is twice the half-integral. -/
lemma Win_even_integral {β : ℝ} (hβ1 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1) :
    (∫ s in ((-1:ℝ)/4)..(1/4), Win β s) = 2 * (∫ s in (0:ℝ)..(1/4), Win β s) := by
  have heq : ((-1:ℝ)/4) = (-(1/4):ℝ) := by norm_num
  have hInt0 : IntervalIntegrable (Win β) volume (0:ℝ) (1/4) := Win_int_right hβ1 hβ2
  have hInt2 : IntervalIntegrable (Win β) volume (-(1/4):ℝ) (0:ℝ) := by
    have h1 : IntervalIntegrable (fun x : ℝ => Win β (-x)) volume (0:ℝ) (1/4) := by
      have : (fun x : ℝ => Win β (-x)) = Win β := by funext x; exact Win_neg β x
      rw [this]; exact hInt0
    have hh := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => Win β (-x))
      (a := (1/4:ℝ)) (b := (0:ℝ))).mp h1.symm
    simpa [one_mul] using hh
  have hsym : (∫ s in (-(1/4):ℝ)..(0:ℝ), Win β s) = (∫ s in (0:ℝ)..(1/4), Win β s) := by
    have h := intervalIntegral.integral_comp_neg (f := Win β) (a := (0:ℝ)) (b := (1/4:ℝ))
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro s hs
    exact Win_neg β s
  rw [heq]
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt2 hInt0, hsym]
  ring
/-! ### The closed-form second derivative and its lower bound -/

/-- `K(b) = 2c/b + c²/b³ + 3c³/(2b⁵)`, `c = b-1`. -/
noncomputable def Kf (b : ℝ) : ℝ :=
  2*(b-1)/b + (b-1)*(b-1)/(b*b*b) + 3*((b-1)*(b-1)*(b-1))/(2*(b*b*b*b*b))
/-- `K'(b)`. -/
noncomputable def Kfp (b : ℝ) : ℝ := (2*b^4 + 2*b^3 + 21*b^2 - 36*b + 15)/(2*b^6)
/-- `K''(b)`. -/
noncomputable def Kfpp (b : ℝ) : ℝ := -(2*b^4 + 3*b^3 + 42*b^2 - 90*b + 45)/b^7

/-- `Gform` written with the logarithm arguments in the `8b+1/(8b)` form. -/
lemma Gform_alt {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) :
    Gform β =
      (13/5)*(Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)))
      + ( (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
          + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
          + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) )
      - ( (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log (8*(2-β)+1/(8*(2-β)))
          + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) )
      - ( (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log (8*β+1/(8*β))
          + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
          + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) ) := by
  unfold Gform
  have hb : (2-β) ≠ 0 := by linarith
  have hb2 : β ≠ 0 := ne_of_gt hβ0
  rw [show (4*(2-β)^2+(1/4)^2)/(2*(2-β)*(1/4)) = 8*(2-β)+1/(8*(2-β)) by
        field_simp; ring,
      show (4*β^2+(1/4)^2)/(2*β*(1/4)) = 8*β+1/(8*β) by
        field_simp; ring]

/-- Lower bound for the target-minus-majorant integral over `[-1/4,1/4]`. -/
theorem boxWindow_C_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (-53:ℝ)/100 ≤ ∫ s in (-1/4 : ℝ)..(1/4),
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
        - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) ) := by
  change (-53:ℝ)/100 ≤ ∫ s in (-1/4 : ℝ)..(1/4), Win β s
  rcases lt_or_ge β ((1:ℝ)/4) with h | h
  · have hb := Commons.Analysis.Integral.boxWin_small_beta hβ0 h.le
    rw [show ((-1:ℝ)/4) = (-4:ℝ)⁻¹ by norm_num] at hb ⊢
    convert hb using 1
    apply intervalIntegral.integral_congr
    intro s hs
    rfl
  · rw [Win_even_integral h hβ1.le, integral_Win h hβ1.le, Gform_alt hβ0 (by linarith)]
    have hG := Commons.Analysis.Integral.Gform_lower h hβ1.le
    linarith

end Commons.Analysis.Integral
