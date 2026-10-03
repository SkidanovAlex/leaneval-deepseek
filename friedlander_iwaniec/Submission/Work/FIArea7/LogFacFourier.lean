/-
# `Submission.Work.FIArea7.LogFacFourier` — the Fourier expansion of the logarithmic factor (7.10)

*FI* (16.7)–(16.9) mollify `logFac z₁ z₂ = log 2|z₁z₂/Δ|` by inserting the Fourier series of
`u(α) = −h(α)log(½|sin α|)`; the resulting expansion `logFac = Σ_k û(k)(z₁z̄₂/|z₁z₂|)^k` is what turns
the pair coefficient of (17.9) into a *product* — the input of the §16 character expansion
`section16_omegaDetect_expansion`.

Here we record the underlying **classical (un-mollified) expansion**, which by
`Work.FIArea7.logFac_eq_arg` reduces to the log-sine series `Σ_n cos(2nt)/n + 2log2` of
`log(2/|sin t|)`, `t = arg z₂ − arg z₁`:

* `Work.FIArea7.logFac_eq_sum_cos` — the truncated form with the explicit remainder `4/(K|sin t|)`;
* `Work.FIArea7.logFac_eq_sum_powers` — the *product form* with the summand
  `(z₂z̄₁/(|z₁||z₂|))^{2n}`, which factors as a function of `z₁` times a function of `z₂`.

The mollified version of *FI* (16.8)/(16.9) (with `û(k) ≪ (1+k²H⁻²)⁻¹log H` and the diagonal
cut-off `O(H⁻¹N²)`) is the next step; the constant term `2log2` and the even frequencies here are
the un-mollified specialisation.
-/
import Mathlib
import Submission.Work.FIArea7.LogFacArg
import Submission.Work.FIArea7.abs_sum_cos_div_le

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open LogFacArg
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma sin_arg_diff_ne_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) ≠ 0 := by
  rw [sin_arg_sub h]
  exact div_ne_zero (by exact_mod_cast h) (norm_mul_ne_zero_of_delta_ne_zero h)

/-- **Truncated expansion of `logFac`**: `logFac = 2log2 + Σ_{n≤K}cos(2nt)/n + O(1/(K|sin t|))`
with the explicit remainder `4/(K|sin t|)`, `t = arg z₂ − arg z₁`. -/
theorem logFac_eq_sum_cos (z1 z2 : GaussianInt) (K : ℕ) (hK : 1 ≤ K)
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    |Work.FITop3.logFac z1 z2 - (2 * Real.log 2
        + ∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n : ℝ) * (Complex.arg z2.toComplex - Complex.arg z1.toComplex))
              / (n : ℝ))|
      ≤ 4 / ((K : ℝ)
        * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
  have hs : Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) ≠ 0 :=
    sin_arg_diff_ne_zero h
  have hs2 : Real.sin (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex) / 2) ≠ 0 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]; exact hs
  have hb := abs_sum_cos_div_le (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) K hK hs2
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hb
  rw [logFac_eq_arg (z1 := z1) (z2 := z2) h]
  have hsin : 0 < |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| := abs_pos.mpr hs
  have hlog : Real.log (2 / |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|)
      = 2 * Real.log 2
        - Real.log (2 * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
    rw [Real.log_div (by norm_num) hsin.ne', Real.log_mul (by norm_num) hsin.ne']
    ring
  rw [hlog]
  have hsum : (∑ n ∈ Finset.Icc 1 K,
        Real.cos (2 * (n : ℝ) * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) / (n : ℝ))
      = ∑ n ∈ Finset.Icc 1 K,
          Real.cos ((n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
            / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * (n : ℝ) * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)
        = (n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) from by ring]
  rw [hsum]
  have hgoal : |(2 * Real.log 2
          - Real.log (2 * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|))
        - (2 * Real.log 2 + ∑ n ∈ Finset.Icc 1 K,
            Real.cos ((n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
              / (n : ℝ))|
      = |(∑ n ∈ Finset.Icc 1 K,
            Real.cos ((n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
              / (n : ℝ))
          + Real.log (2 * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|)| := by
    rw [show (2 * Real.log 2
            - Real.log (2 * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|))
          - (2 * Real.log 2 + ∑ n ∈ Finset.Icc 1 K,
              Real.cos ((n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
                / (n : ℝ))
        = -((∑ n ∈ Finset.Icc 1 K,
              Real.cos ((n : ℝ) * (2 * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
                / (n : ℝ))
            + Real.log (2 * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|))
        from by ring]
    rw [abs_neg]
  rw [hgoal]
  exact hb

/-! ## The polar decomposition of the ratio `z₂z̄₁/(|z₁||z₂|)` -/

lemma exp_arg_mul_I (x : ℂ) (hx : x ≠ 0) :
    Complex.exp ((x.arg : ℝ) * Complex.I) = x / ((‖x‖ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, eq_div_iff]
  · rw [mul_comm]; exact Complex.norm_mul_cos_add_sin_mul_I x
  · exact_mod_cast (norm_ne_zero_iff.mpr hx)

lemma exp_neg_arg_mul_I (x : ℂ) (hx : x ≠ 0) :
    Complex.exp (-((x.arg : ℝ) * Complex.I)) = star x / ((‖x‖ : ℝ) : ℂ) := by
  have h := exp_arg_mul_I x hx
  have hconj : star (Complex.exp ((x.arg : ℝ) * Complex.I))
      = Complex.exp (-((x.arg : ℝ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  rw [← hconj, h, star_div₀]
  simp

/-- **`(z₂z̄₁/(|z₁||z₂|))^k` is a unit complex number of argument `k(arg z₂ − arg z₁)`**, so its real
part is `cos(k(arg z₂ − arg z₁))`.  This is the identity that makes the expansion of `logFac` a sum
of products of a function of `z₁` and a function of `z₂`. -/
lemma ratio_pow_re (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    (((a * star b) / ((‖b‖ * ‖a‖ : ℝ) : ℂ)) ^ k).re
      = Real.cos ((k : ℝ) * (a.arg - b.arg)) := by
  have hfac : (a * star b) / ((‖b‖ * ‖a‖ : ℝ) : ℂ)
      = (a / ((‖a‖ : ℝ) : ℂ)) * (star b / ((‖b‖ : ℝ) : ℂ)) := by
    push_cast
    ring
  have h1 := exp_arg_mul_I a ha
  have h2 := exp_neg_arg_mul_I b hb
  have hw : (a / ((‖a‖ : ℝ) : ℂ)) * (star b / ((‖b‖ : ℝ) : ℂ))
      = Complex.exp (((a.arg - b.arg : ℝ)) * Complex.I) := by
    rw [← h1, ← h2, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, hw, ← Complex.exp_nat_mul]
  rw [show (k : ℂ) * ((↑(a.arg - b.arg) : ℂ) * Complex.I)
      = ((↑((k : ℝ) * (a.arg - b.arg)) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  ring

/-- **The product form**: the truncated sum of `logFac` is a sum of powers
`(z₂z̄₁/(|z₁||z₂|))^{2n}`, whose summand factors as `(z₂/|z₂|)^{2n}·(z̄₁/|z₁|)^{2n}` — a function of
`z₂` times a function of `z₁`.  This is the shape the §16 character expansion consumes. -/
theorem logFac_eq_sum_powers (z1 z2 : GaussianInt) (K : ℕ) (hK : 1 ≤ K)
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    |Work.FITop3.logFac z1 z2 - (2 * Real.log 2
        + ∑ n ∈ Finset.Icc 1 K,
            (1 / (n : ℝ)) *
              ((((z2.toComplex * star z1.toComplex)
                / ((‖z1.toComplex‖ * ‖z2.toComplex‖ : ℝ) : ℂ)) ^ (2 * (n : ℕ))).re))|
      ≤ 4 / ((K : ℝ)
        * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
  have hz1 : z1 ≠ 0 := by
    rintro rfl
    simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by
    rintro rfl
    simp [Work.FIPlan.Delta] at h
  have hz1c : z1.toComplex ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)
  have hz2c : z2.toComplex ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)
  have hcongr : (∑ n ∈ Finset.Icc 1 K,
        (1 / (n : ℝ)) *
          ((((z2.toComplex * star z1.toComplex)
            / ((‖z1.toComplex‖ * ‖z2.toComplex‖ : ℝ) : ℂ)) ^ (2 * (n : ℕ))).re))
      = ∑ n ∈ Finset.Icc 1 K,
          Real.cos (2 * (n : ℝ)
            * (Complex.arg z2.toComplex - Complex.arg z1.toComplex)) / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ratio_pow_re z2.toComplex z1.toComplex hz2c hz1c (2 * n)]
    have harg : ((2 * n : ℕ) : ℝ) * ((z2.toComplex).arg - (z1.toComplex).arg)
        = 2 * (n : ℝ) * ((z2.toComplex).arg - (z1.toComplex).arg) := by
      push_cast; ring
    rw [harg]
    ring
  rw [hcongr]
  exact logFac_eq_sum_cos z1 z2 K hK h

end

end Work.FIArea7
