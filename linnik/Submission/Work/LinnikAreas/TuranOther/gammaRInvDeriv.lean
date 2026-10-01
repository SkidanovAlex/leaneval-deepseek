import Mathlib
import Submission.Work.LinnikAreas.TuranOther.gammaRDerivSeries
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries

/-!
# The `k`-th derivative of `logDeriv (Γ_ℝ(· + a))⁻¹`

For `k ≥ 1`, `a ∈ {0,1}` and `1 < t.re` we prove

`(logDeriv (z ↦ (Γ_ℝ (z + a))⁻¹))^{(k)}(t) = (-1)^k k! ∑_{n ≥ 0} (t + a + 2n)^{-(k+1)}`.

The logarithmic derivative of the reciprocal is the negative of `logDeriv Γ_ℝ` shifted by `a`
(`logDeriv_inv_comp`), so the chain rule along `z ↦ z + a`
(`iteratedDeriv_comp_add_const`) reduces the claim to the Hurwitz-zeta series for the
derivatives of `logDeriv Γ_ℝ` (`gammaRDerivSeries`), followed by the elementary reindexing
`(1/X)^{k+1} = X^{-(k+1)}`.
-/

namespace Work.LinnikAreas.TuranOther

open Filter

/-- `logDeriv` of a reciprocal: for differentiable `h` with `h s ≠ 0`,
`logDeriv (fun u => (h u)⁻¹) s = - logDeriv h s`. -/
private lemma logDeriv_inv' (h : ℂ → ℂ) (s : ℂ) (hd : DifferentiableAt ℂ h s) (hne : h s ≠ 0) :
    logDeriv (fun u => (h u)⁻¹) s = - logDeriv h s := by
  have hderiv : deriv (fun u => (h u)⁻¹) s = - deriv h s / (h s) ^ 2 := by
    change deriv h⁻¹ s = - deriv h s / (h s) ^ 2
    exact (hd.hasDerivAt.inv hne).deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv]
  field_simp

/-- The same identity with the differentiability hypothesis placed on the reciprocal; this is
the form needed when the function itself is only known to be differentiable through its
reciprocal (as for `Γ_ℝ`). -/
private lemma logDeriv_inv_comp (h : ℂ → ℂ) {s : ℂ}
    (hd : DifferentiableAt ℂ (fun u => (h u)⁻¹) s) (hne : h s ≠ 0) :
    logDeriv (fun u => (h u)⁻¹) s = - logDeriv h s := by
  have hh : DifferentiableAt ℂ h s := by
    have h2 := hd.hasDerivAt.inv (inv_ne_zero hne)
    have heq : (fun u : ℂ => (h u)⁻¹)⁻¹ = h := by funext u; simp
    rw [heq] at h2
    exact h2.differentiableAt
  exact logDeriv_inv' h s hh hne

theorem gammaRInvDeriv (a : ℕ) (ha : a = 0 ∨ a = 1) (k : ℕ) (hk : 1 ≤ k) {t : ℂ}
    (ht : 1 < t.re) :
    iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t =
      (-1 : ℂ) ^ k * (k.factorial : ℂ)
        * (∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) := by
  have hwre : 0 < (t + (a : ℂ)).re := by
    have ha' : (0 : ℝ) ≤ (a : ℂ).re := by simp
    rw [Complex.add_re]; linarith
  have hdiff : Differentiable ℂ (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (a : ℂ))
  -- Step 1: the reciprocal `z ↦ (Γ_ℝ (z+a))⁻¹` has logarithmic derivative
  -- `- logDeriv (fun u => Γ_ℝ (u + a))`
  have hfun : logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)
      =ᶠ[nhds t] fun z : ℂ => - logDeriv (fun u : ℂ => Complex.Gammaℝ (u + a)) z := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (by linarith : 0 < t.re)] with z hz
    have hzre : 0 < (z + (a : ℂ)).re := by
      have ha' : (0 : ℝ) ≤ (a : ℂ).re := by simp
      rw [Complex.add_re]; linarith
    exact logDeriv_inv_comp (fun u : ℂ => Complex.Gammaℝ (u + a))
      hdiff.differentiableAt (Complex.Gammaℝ_ne_zero_of_re_pos hzre)
  -- Step 2: shift the argument by `a`
  have hF : logDeriv (fun u : ℂ => Complex.Gammaℝ (u + a))
      = fun z : ℂ => logDeriv Complex.Gammaℝ (z + a) := by
    funext z
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]
  rw [hfun.iteratedDeriv_eq k, iteratedDeriv_fun_neg, hF, iteratedDeriv_comp_add_const]
  simp only []
  -- Step 3: the Hurwitz-zeta series for `(logDeriv Γ_ℝ)^{(k)}`
  have hGS : iteratedDeriv k (logDeriv Complex.Gammaℝ) (t + (a : ℂ))
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
          * ∑' n : ℕ, (1 / (t + (a : ℂ) + 2 * (n : ℂ))) ^ (k + 1) := by
    simpa only using gammaRDerivSeries (t := t + (a : ℂ)) k hk hwre
  rw [hGS]
  -- Step 4: reindexing `(1 / X)^{k+1} = X^{-(k+1)}`
  have hterm : ∀ n : ℕ, (1 / (t + (a : ℂ) + 2 * (n : ℂ))) ^ (k + 1)
      = (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) := by
    intro n
    rw [one_div, inv_pow,
      show (-(k + 1) : ℤ) = -(((k + 1 : ℕ)) : ℤ) by omega, zpow_neg, zpow_natCast]
  rw [tsum_congr hterm]
  rw [pow_succ]
  ring

end Work.LinnikAreas.TuranOther
