import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- Explicit evaluation of the weighted integral appearing in the switched
(AP) upper-bound main term.  The antiderivative is
`u ↦ -12 log(u+2) + 36/(u+2)^2 + (28/3) log u`, whose derivative is the
integrand on `[2,4]` (the integrand equals
`-12/(u+2) - 72/(u+2)^3 + 28/(3u)` there). -/
theorem integral_L1lo :
    ∫ u in (2 : ℝ)..4, (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u
      = -5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) 4,
      HasDerivAt (fun u : ℝ => -12 * Real.log (u + 2) + 36 / (u + 2) ^ 2 + (28 / 3) * Real.log u)
        ((2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hu
    have hu0 : (0 : ℝ) < u := by linarith [(Set.mem_Icc.mp hu).1]
    have hlog : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (u + 2)) u := by
      have h := ((hasDerivAt_id u).add_const 2).log (by positivity)
      have hfun : (fun y : ℝ => Real.log (id y + 2)) = (fun y : ℝ => Real.log (y + 2)) := by
        funext y; rfl
      rw [hfun] at h
      simpa using h
    have h1 : HasDerivAt (fun u : ℝ => -12 * Real.log (u + 2)) (-12 * (1 / (u + 2))) u :=
      hlog.const_mul (-12)
    have h2 : HasDerivAt (fun u : ℝ => 36 / (u + 2) ^ 2) (-72 / (u + 2) ^ 3) u := by
      have hden : HasDerivAt (fun y : ℝ => (y + 2) ^ 2) (2 * (u + 2)) u := by
        have h := ((hasDerivAt_id u).add_const 2).pow 2
        have hfun : ((fun x : ℝ => id x + 2) ^ 2) = (fun y : ℝ => (y + 2) ^ 2) := by
          funext y; simp [Pi.pow_apply]
        rw [hfun] at h
        simpa using h
      have hne : (u + 2) ^ 2 ≠ 0 := by positivity
      have h := (hasDerivAt_const u (36 : ℝ)).div hden hne
      have hfun2 : ((fun _ : ℝ => (36 : ℝ)) / (fun y : ℝ => (y + 2) ^ 2)) =
          (fun y : ℝ => 36 / (y + 2) ^ 2) := by
        funext y; rw [Pi.div_apply]
      rw [hfun2] at h
      have key : -(36 * (2 * (u + 2))) / ((u + 2) ^ 2) ^ 2 = -72 / (u + 2) ^ 3 := by
        field_simp
        ring
      simpa [key] using h
    have h3 : HasDerivAt (fun u : ℝ => (28 / 3) * Real.log u) ((28 / 3) * u⁻¹) u := by
      have := (Real.hasDerivAt_log (ne_of_gt hu0)).const_mul (28 / 3)
      simpa using this
    have hcomb := (h1.add h2).add h3
    have hfun_eq : (((fun u : ℝ => -12 * Real.log (u + 2)) + fun u => 36 / (u + 2) ^ 2) +
          fun u => (28 / 3) * Real.log u)
        = (fun u : ℝ => -12 * Real.log (u + 2) + 36 / (u + 2) ^ 2 + (28 / 3) * Real.log u) := by
      funext y; simp [Pi.add_apply]
    rw [hfun_eq] at hcomb
    have key : -(12 * (u + 2)⁻¹) + -72 / (u + 2) ^ 3 + 28 / 3 * u⁻¹
        = (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u := by
      field_simp
      ring
    simpa [key] using hcomb
  have hcont : ContinuousOn
      (fun u : ℝ => (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u)
      (Set.uIcc 2 4) := by
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    apply ContinuousOn.div
    · apply ContinuousOn.add
      · apply ContinuousOn.const_mul
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
      · apply ContinuousOn.const_mul
        apply ContinuousOn.pow
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
    · fun_prop
    · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  norm_num
  rw [h6, h4]
  ring

end Work.NumberTheory.Chen.APSwitchUpper
