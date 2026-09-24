import Mathlib
import Submission.Work.GM.S3.hhat_defs

/-!
# Iterated derivatives of the oscillatory factor `phi t u = u^{it}`

`phi t u = exp (i t log u)` (see `Submission/Work/GM/S3/hhat_defs.lean`).  On the positive
reals this is `u ↦ u^{it}`, and differentiating `k` times brings down the falling factor
`(it)(it-1)···(it-k+1)` and one factor `u^{-1}` each time:

  `(d/du)^k (u^{it}) = (∏_{i<k} (it - i)) · u^{it-k}`
                     = `(∏_{i<k} (it - i)) · exp((it - k) log u)`.

This file proves exactly that (`phi_iteratedDeriv`) as requested, via the general one-parameter
family `fun u => exp (c * log u)` (`iteratedDeriv_exp_mul_log`), which is stated for an
arbitrary complex `c`.
-/

namespace Work.GM.S3

open Complex Finset
open scoped BigOperators Topology

/-- For `x > 0`, `exp (log x) = x` for the complex exponential applied to the real logarithm. -/
theorem cexp_ofReal_log {x : ℝ} (hx : 0 < x) :
    Complex.exp ((Real.log x : ℝ) : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

/-- For `x > 0`, `x⁻¹ = exp (-(log x))` in `ℂ`. -/
theorem inv_eq_cexp_neg_log {x : ℝ} (hx : 0 < x) :
    ((x : ℂ))⁻¹ = Complex.exp (-(Real.log x : ℂ)) := by
  rw [Complex.exp_neg, cexp_ofReal_log hx]

/-- The derivative of `u ↦ exp (c · log u)` at a positive point `x`. -/
theorem hasDerivAt_cexp_mul_log (c : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ)))
      (Complex.exp (c * (Real.log x : ℂ)) * (c * (x : ℂ)⁻¹)) x := by
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have h2 : HasDerivAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    h1.ofReal_comp
  have h3 : HasDerivAt (fun u : ℝ => c * ((Real.log u : ℝ) : ℂ)) (c * ((x⁻¹ : ℝ) : ℂ)) x :=
    h2.const_mul c
  have h4 : HasDerivAt (fun u : ℝ => Complex.exp (c * ((Real.log u : ℝ) : ℂ)))
      (Complex.exp (c * ((Real.log x : ℝ) : ℂ)) * (c * ((x⁻¹ : ℝ) : ℂ))) x := h3.cexp
  rw [Complex.ofReal_inv] at h4
  exact h4

/-- The `k`-th iterated derivative of `u ↦ exp (c · log u)` at a positive point:
`(∏_{i<k} (c - i)) · exp((c - k) log x)`. -/
theorem iteratedDeriv_cexp_mul_log (c : ℂ) (k : ℕ) :
    ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ))) x
        = (∏ i ∈ Finset.range k, (c - (i : ℂ))) *
          Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) := by
  induction k with
  | zero =>
      intro x _
      simp
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : (fun u => iteratedDeriv k (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ))) u)
          =ᶠ[𝓝 x] (fun u => (∏ i ∈ Finset.range k, (c - (i : ℂ))) *
            Complex.exp ((c - (k : ℂ)) * (Real.log u : ℂ))) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
        exact ih u hu
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hg : HasDerivAt (fun u : ℝ => Complex.exp ((c - (k : ℂ)) * (Real.log u : ℂ)))
          (Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
            ((c - (k : ℂ)) * (x : ℂ)⁻¹)) x :=
        hasDerivAt_cexp_mul_log (c - (k : ℂ)) hx
      rw [deriv_const_mul _ hg.differentiableAt]
      rw [hg.deriv]
      rw [Finset.prod_range_succ, inv_eq_cexp_neg_log hx]
      have key : Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
            ((c - (k : ℂ)) * Complex.exp (-(Real.log x : ℂ)))
          = (c - (k : ℂ)) * Complex.exp ((c - ((k + 1 : ℕ) : ℂ)) * (Real.log x : ℂ)) := by
        have h1 : Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
              ((c - (k : ℂ)) * Complex.exp (-(Real.log x : ℂ)))
            = (c - (k : ℂ)) * (Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
                Complex.exp (-(Real.log x : ℂ))) := by ring
        rw [h1, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
      rw [key]
      ring

/-- `(d/dx)^k (x^{it}) = (∏_{i<k} (it - i)) · x^{it-k}`, i.e. the iterated derivatives of the
oscillatory factor `phi t`. -/
theorem phi_iteratedDeriv (t : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (phi t) x
      = (∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))) *
        Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ)) := by
  have h := iteratedDeriv_cexp_mul_log (Complex.I * (t : ℂ)) k x hx
  have hphi : phi t = fun u : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ)) := rfl
  rw [hphi]
  exact h

end Work.GM.S3
