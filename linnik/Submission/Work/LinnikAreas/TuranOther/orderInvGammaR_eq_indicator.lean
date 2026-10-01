import Mathlib

namespace Work.LinnikAreas.TuranOther

open Complex

/-!
# The order of vanishing of `1 / Γ_ℝ`

We prove that the reciprocal of Deligne's archimedean Gamma factor
`Γ_ℝ(s) = π ^ (-s/2) * Γ(s/2)` has a simple zero exactly at the points `-2n`
(`n : ℕ`) and is non-zero elsewhere, hence

`analyticOrderNatAt (fun s => (Γ_ℝ s)⁻¹) u = 1` on `{0, -2, -4, …}` and `0` off it.
-/

private lemma gammaR_inv_eq : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
    = ((fun s : ℂ => (Real.pi : ℂ) ^ (s/2)) * (fun s : ℂ => (Complex.Gamma (s/2))⁻¹)) := by
  funext s
  rw [Complex.Gammaℝ_def, mul_inv]
  have h1 : (Real.pi : ℂ) ^ (-s/2) = ((Real.pi : ℂ) ^ (s/2))⁻¹ := by
    rw [neg_div, Complex.cpow_neg]
  rw [h1, inv_inv]
  simp only [Pi.mul_apply]

private lemma differentiable_cpow_half :
    Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s/2)) :=
  (differentiable_id.div_const (2:ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

private lemma analyticAt_cpow_half (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s/2)) z :=
  differentiable_cpow_half.analyticAt z

private lemma ord_cpow_half (z : ℂ) :
    analyticOrderAt (fun s : ℂ => (Real.pi : ℂ) ^ (s/2)) z = 0 := by
  rw [AnalyticAt.analyticOrderAt_eq_zero (analyticAt_cpow_half z)]
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))

private lemma differentiable_invGamma_half :
    Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s/2))⁻¹) :=
  Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2)

private lemma analyticAt_invGamma_half (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (Complex.Gamma (s/2))⁻¹) z :=
  differentiable_invGamma_half.analyticAt z

private lemma deriv_div_two (z : ℂ) : deriv (fun s : ℂ => s/2) z ≠ 0 := by
  rw [deriv_div_const]
  rw [show deriv (fun s : ℂ => s) z = 1 from by simp]
  norm_num

private lemma ord_invGamma_half (z : ℂ) :
    analyticOrderAt (fun s : ℂ => (Complex.Gamma (s/2))⁻¹) z
      = analyticOrderAt (fun t : ℂ => (Complex.Gamma t)⁻¹) (z/2) := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun t : ℂ => (Complex.Gamma t)⁻¹) (g := fun s : ℂ => s/2) (z₀ := z)
    (by fun_prop) (deriv_div_two z)
  simpa only [Function.comp_def] using h

private lemma invGamma_eq_key : (fun t : ℂ => (Complex.Gamma t)⁻¹)
    = ((fun t : ℂ => t) * (fun t : ℂ => (Complex.Gamma (t+1))⁻¹)) := by
  funext t; exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one t

private lemma analyticAt_invGamma (z : ℂ) : AnalyticAt ℂ (fun t : ℂ => (Complex.Gamma t)⁻¹) z :=
  Complex.differentiable_one_div_Gamma.analyticAt z

private lemma analyticAt_invGamma_shift (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => (Complex.Gamma (t+1))⁻¹) z := by
  apply Differentiable.analyticAt
  exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)

private lemma deriv_shift (z : ℂ) : deriv (fun t : ℂ => t+1) z ≠ 0 := by
  rw [deriv_add_const]
  rw [show deriv (fun t : ℂ => t) z = 1 from by simp]
  norm_num

private lemma ord_invGamma_shift (z : ℂ) :
    analyticOrderAt (fun t : ℂ => (Complex.Gamma (t+1))⁻¹) z
      = analyticOrderAt (fun t : ℂ => (Complex.Gamma t)⁻¹) (z+1) := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun t : ℂ => (Complex.Gamma t)⁻¹) (g := fun t : ℂ => t+1) (z₀ := z)
    (by fun_prop) (deriv_shift z)
  simpa only [Function.comp_def] using h

private lemma ord_invGamma_one : analyticOrderAt (fun t : ℂ => (Complex.Gamma t)⁻¹) 1 = 0 := by
  rw [AnalyticAt.analyticOrderAt_eq_zero (analyticAt_invGamma 1)]
  simp [Complex.Gamma_one]

private lemma ord_id_zero : analyticOrderAt (fun t : ℂ => t) (0:ℂ) = 1 :=
  analyticOrderAt_id

private lemma ord_id_ne {z : ℂ} (hz : z ≠ 0) : analyticOrderAt (fun t : ℂ => t) z = 0 :=
  analyticOrderAt_eq_zero.mpr (Or.inr hz)

private lemma ord_invGamma_neg (n : ℕ) :
    analyticOrderAt (fun t : ℂ => (Complex.Gamma t)⁻¹) (-(n:ℂ)) = 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, neg_zero]
    rw [invGamma_eq_key, analyticOrderAt_mul (by fun_prop) (analyticAt_invGamma_shift 0),
      ord_id_zero]
    rw [ord_invGamma_shift 0]
    rw [show (0:ℂ)+1 = 1 from by simp, ord_invGamma_one]
    norm_num
  | succ n ih =>
    have hz : (-(↑(n+1) : ℂ)) ≠ 0 := by
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    rw [invGamma_eq_key, analyticOrderAt_mul (by fun_prop) (analyticAt_invGamma_shift _)]
    rw [ord_id_ne hz]
    rw [ord_invGamma_shift]
    have hcast : (-(↑(n+1) : ℂ)) + 1 = -(↑n : ℂ) := by push_cast; ring
    rw [hcast, ih]
    norm_num

-- Route: `(Gammaℝ ·)⁻¹ = (fun s => π ^ (s/2) * (Complex.Gamma (s/2))⁻¹)` is entire
-- (`Complex.differentiable_one_div_Gamma`), its zeros are exactly the set in the indicator
-- (`Complex.Gammaℝ_eq_zero_iff`), and each such zero is simple: iterate
-- `Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one` (order 1 at `0`, hence at every `-m`),
-- analytically (`analyticOrderAt_mul`).
theorem orderInvGammaR_eq_indicator (u : ℂ) :
    analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u
      = (Set.range (fun n : ℕ => -((2 * n : ℕ) : ℂ))).indicator (fun _ => (1 : ℕ)) u := by
  have hF : analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u
      = analyticOrderAt (fun t : ℂ => (Complex.Gamma t)⁻¹) (u/2) := by
    rw [gammaR_inv_eq, analyticOrderAt_mul (analyticAt_cpow_half u) (analyticAt_invGamma_half u),
      ord_cpow_half, ord_invGamma_half]
    simp
  by_cases h : u ∈ Set.range (fun n : ℕ => -((2 * n : ℕ) : ℂ))
  · rw [Set.indicator_of_mem h]
    obtain ⟨m, hm⟩ := h
    have hm' : u = -((2 * m : ℕ) : ℂ) := by simpa using hm.symm
    have h1 : analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u = 1 := by
      rw [hF, hm']
      rw [show (-((2*m : ℕ) : ℂ))/2 = -(m:ℂ) from by
        have hh : ((2*m : ℕ) : ℂ) = 2 * (m:ℂ) := by simp [Nat.cast_mul]
        rw [hh]; ring]
      exact ord_invGamma_neg m
    simp [analyticOrderNatAt, h1]
  · rw [Set.indicator_of_notMem h]
    have hcon : ∀ m : ℕ, u/2 ≠ -(m:ℂ) := by
      intro m hm
      apply h
      refine ⟨m, ?_⟩
      have h2 : u = 2 * (u/2) := by
        rw [mul_comm, div_mul_cancel₀ u (two_ne_zero : (2:ℂ) ≠ 0)]
      rw [h2, hm]
      show -((2*m : ℕ) : ℂ) = 2 * -(m:ℂ)
      have hh : ((2*m : ℕ) : ℂ) = 2 * (m:ℂ) := by simp [Nat.cast_mul]
      rw [hh]; ring
    have h0 : analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u = 0 := by
      rw [hF, AnalyticAt.analyticOrderAt_eq_zero (analyticAt_invGamma (u/2))]
      exact inv_ne_zero (Complex.Gamma_ne_zero hcon)
    simp [analyticOrderNatAt, h0]

end Work.LinnikAreas.TuranOther
