import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.kappa_exp_fourier

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral

/-!
# The Fourier/Mellin decay bound for the logarithmic trapezoid weight `mwt`

This file proves

`‖∫_{X e^{-1}}^{X e^{3}} mwt(X,x) · x^{4+iΔ} dx‖ ≤ e^{-4}(1+e^{5}+e^{20}+e^{15}) X^{5}/(1+Δ^{2})`.

The proof is by an explicit change of variables.  Writing `x = X e^{u-1}` and putting
`Z = 5 + iΔ`, the integral equals `X^Z e^{-Z} · ∫_0^4 κ(u) e^{Zu} du`, and the remaining
integral is the exponential Fourier transform of the trapezoid weight `κ`, which equals
`(e^{4Z} - e^{3Z} - e^{Z} + 1)/Z^{2}` (`Work.BMF.kappa_exp_fourier`).  Bounding each factor
by its modulus gives the claim.

## Main auxiliary results

* `Work.BMF.kappa_eq_clamp_glue`, `Work.BMF.continuous_kappa_glue`: `κ` is the clamp
  `min 1 (max 0 (min w (4-w)))`, hence continuous.
* `Work.BMF.mwt_transform_reduce_glue`: the change of variables.
-/

/-- The trapezoid weight `κ` is the clamp of `w` into `[0,1]` in the logarithmic variable:
`κ w = min 1 (max 0 (min w (4 - w)))`. -/
lemma kappa_eq_clamp_glue (w : ℝ) : kappa w = min 1 (max 0 (min w (4 - w))) := by
  unfold kappa
  by_cases h0 : w ≤ 0
  · rw [if_pos h0, min_eq_left (by linarith : w ≤ 4 - w), max_eq_left h0,
      min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  · rw [if_neg h0]
    by_cases h1 : w ≤ 1
    · rw [if_pos h1, min_eq_left (by linarith : w ≤ 4 - w), max_eq_right (by linarith : (0:ℝ) ≤ w),
        min_eq_right h1]
    · rw [if_neg h1]
      by_cases h3 : w ≤ 3
      · rw [if_pos h3]
        by_cases h2 : w ≤ 2
        · rw [min_eq_left (by linarith : w ≤ 4 - w), max_eq_right (by linarith : (0:ℝ) ≤ w),
            min_eq_left (by linarith : (1:ℝ) ≤ w)]
        · rw [min_eq_right (by linarith : 4 - w ≤ w), max_eq_right (by linarith : (0:ℝ) ≤ 4 - w),
            min_eq_left (by linarith : (1:ℝ) ≤ 4 - w)]
      · rw [if_neg h3]
        by_cases h4 : w ≤ 4
        · rw [if_pos h4, min_eq_right (by linarith : 4 - w ≤ w),
            max_eq_right (by linarith : (0:ℝ) ≤ 4 - w), min_eq_right (by linarith : 4 - w ≤ 1)]
        · rw [if_neg h4, min_eq_right (by linarith : 4 - w ≤ w),
            max_eq_left (by linarith : 4 - w ≤ 0), min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

/-- The trapezoid weight `κ` is continuous. -/
lemma continuous_kappa_glue : Continuous kappa := by
  rw [funext kappa_eq_clamp_glue]
  fun_prop

/-- **Change of variables in the Mellin transform of `mwt`.**
For `X > 0` and real `Δ`, substituting `x = X e^{u-1}` (so that `mwt X x = κ u` and
`x^{4+iΔ} dx = X^{5+iΔ} e^{-(5+iΔ)} e^{(5+iΔ)u} du`) gives
`∫_{X e^{-1}}^{X e^{3}} mwt(X,x) x^{4+iΔ} dx
   = X^{5+iΔ} e^{-(5+iΔ)} ∫_0^4 κ(u) e^{(5+iΔ)u} du`. -/
lemma mwt_transform_reduce_glue (X Δ : ℝ) (hX : 0 < X) :
    (∫ x in X * Real.exp (-1)..X * Real.exp 3, (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ)))
      = (X:ℂ)^(5 + Complex.I*(Δ:ℂ)) * Complex.exp (-(5 + Complex.I*(Δ:ℂ)))
          * ∫ u in (0:ℝ)..4, (kappa u : ℂ) * Complex.exp ((5 + Complex.I*(Δ:ℂ)) * (u:ℂ)) := by
  have hgcIcc : ContinuousOn (fun x : ℝ => (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ)))
      (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3)) := by
    apply ContinuousOn.mul
    · have hlogx : ContinuousOn (fun x : ℝ => Real.log (x / X))
          (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3)) := by
        apply ContinuousOn.log
        · fun_prop
        · intro x hx
          have h1 : 0 < X * Real.exp (-1) := by positivity
          exact div_ne_zero (by linarith [hx.1, h1]) hX.ne'
      have hlog1 : ContinuousOn (fun x : ℝ => Real.log (x / X) + 1)
          (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3)) :=
        hlogx.add (continuousOn_const (c := (1:ℝ)))
      have hcomp : ContinuousOn (fun x : ℝ => (kappa (Real.log (x / X) + 1) : ℂ))
          (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3)) :=
        Complex.continuous_ofReal.comp_continuousOn
          (continuous_kappa_glue.comp_continuousOn hlog1)
      simpa [mwt] using hcomp
    · exact (Complex.continuous_ofReal_cpow_const
        (by simp : 0 < (4 + Complex.I*(Δ:ℂ)).re)).continuousOn
  have hgcont : ContinuousOn (fun x : ℝ => (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ)))
      ((fun u : ℝ => X * Real.exp (u - 1)) '' Set.uIcc (0:ℝ) 4) := by
    apply hgcIcc.mono
    rintro x ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 4)] at hu
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu.1])) hX.le,
           mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu.2])) hX.le⟩
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) 4,
      HasDerivAt (fun u : ℝ => X * Real.exp (u - 1)) (X * Real.exp (u - 1)) u := by
    intro u _
    simpa using ((Real.hasDerivAt_exp (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)).const_mul X
  have hcontf : ContinuousOn (fun u : ℝ => X * Real.exp (u - 1)) (Set.uIcc (0:ℝ) 4) := by
    fun_prop
  have hsub := intervalIntegral.integral_deriv_smul_comp'
      (a := (0:ℝ)) (b := 4)
      (f := fun u : ℝ => X * Real.exp (u - 1)) (f' := fun u : ℝ => X * Real.exp (u - 1))
      (g := fun x : ℝ => (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ)))
      hderiv hcontf hgcont
  have hf0 : X * Real.exp (0 - 1) = X * Real.exp (-1) := by norm_num
  have hf4 : X * Real.exp (4 - 1) = X * Real.exp 3 := by norm_num
  rw [hf0, hf4] at hsub
  have hpt : ∀ u : ℝ,
      (X * Real.exp (u - 1)) •
          ((mwt X (X * Real.exp (u - 1)) : ℂ) * ((X * Real.exp (u - 1) : ℝ):ℂ)^(4 + Complex.I*(Δ:ℂ)))
      = ((X:ℂ)^(5 + Complex.I*(Δ:ℂ)) * Complex.exp (-(5 + Complex.I*(Δ:ℂ)))) *
          ((kappa u : ℂ) * Complex.exp ((5 + Complex.I*(Δ:ℂ)) * (u:ℂ))) := by
    intro u
    have hmwt : mwt X (X * Real.exp (u - 1)) = kappa u := by
      unfold mwt
      have h : X * Real.exp (u - 1) / X = Real.exp (u - 1) := by field_simp
      rw [h, Real.log_exp]; ring_nf
    have hb : ((X * Real.exp (u - 1) : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]; positivity
    have hX0 : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    have h1 : ((X * Real.exp (u - 1) : ℝ) : ℂ) *
          ((X * Real.exp (u - 1) : ℝ) : ℂ)^(4 + Complex.I*(Δ:ℂ))
        = ((X * Real.exp (u - 1) : ℝ) : ℂ)^(5 + Complex.I*(Δ:ℂ)) := by
      have h := Complex.cpow_add (x := ((X * Real.exp (u - 1) : ℝ) : ℂ)) (y := (1:ℂ))
        (z := (4 + Complex.I*(Δ:ℂ))) hb
      rw [Complex.cpow_one] at h
      rw [← h]; congr 1; ring
    have h2 : ((X * Real.exp (u - 1) : ℝ) : ℂ)^(5 + Complex.I*(Δ:ℂ))
        = (X:ℂ)^(5 + Complex.I*(Δ:ℂ)) * Complex.exp (-(5 + Complex.I*(Δ:ℂ))) *
          Complex.exp ((5 + Complex.I*(Δ:ℂ))*(u:ℂ)) := by
      set Z : ℂ := 5 + Complex.I*(Δ:ℂ) with hZ
      rw [Complex.cpow_def_of_ne_zero hb,
        ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ X * Real.exp (u - 1))]
      rw [Real.log_mul hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      rw [Complex.ofReal_log hX.le, ← Complex.cpow_def_of_ne_zero hX0]
      have h3 : Complex.exp (((u-1:ℝ):ℂ) * Z) = Complex.exp (-Z) * Complex.exp (Z*(u:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [h3]; ring
    rw [Complex.real_smul, hmwt, ← mul_assoc,
      mul_comm (((X * Real.exp (u - 1) : ℝ)):ℂ) (kappa u : ℂ), mul_assoc, h1, h2]
    ring
  have hkey : (∫ x in (0:ℝ)..4, (fun u : ℝ => X * Real.exp (u - 1)) x •
        ((fun x : ℝ => (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))) ∘
          (fun u : ℝ => X * Real.exp (u - 1))) x)
      = (X:ℂ)^(5 + Complex.I*(Δ:ℂ)) * Complex.exp (-(5 + Complex.I*(Δ:ℂ)))
          * ∫ u in (0:ℝ)..4, (kappa u : ℂ) * Complex.exp ((5 + Complex.I*(Δ:ℂ)) * (u:ℂ)) := by
    rw [intervalIntegral.integral_congr (fun u _ => by
      simp only [Function.comp_apply]
      exact hpt u)]
    rw [intervalIntegral.integral_const_mul]
  rw [← hsub, hkey]

/-- **Target.** The Mellin transform of the logarithmic trapezoid weight `mwt` decays like
`1/(1+Δ^2)` in the imaginary part of the exponent. -/
theorem mwt_transform_bound (X Δ : ℝ) (hX : 0 < X) :
    ‖∫ x in X * Real.exp (-1)..X * Real.exp 3, (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))‖
      ≤ Real.exp (-4) * (1 + Real.exp 5 + Real.exp 20 + Real.exp 15) * X^5 / (1 + Δ^2) := by
  have hZ : (5 + Complex.I*(Δ:ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hred := mwt_transform_reduce_glue X Δ hX
  have hfou := kappa_exp_fourier (5 + Complex.I*(Δ:ℂ)) hZ
  rw [hred, hfou]
  have hA : ‖(X:ℂ)^(5 + Complex.I*(Δ:ℂ))‖ = X^5 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]; simp
  have hB : ‖Complex.exp (-(5 + Complex.I*(Δ:ℂ)))‖ = Real.exp (-5) := by
    rw [Complex.norm_exp]; simp
  have hC : ‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ))) - Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))
        - Complex.exp (5 + Complex.I*(Δ:ℂ)) + 1‖
      ≤ Real.exp 20 + Real.exp 15 + Real.exp 5 + 1 := by
    have h4 : ‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ)))‖ = Real.exp 20 := by
      rw [Complex.norm_exp]; simp; norm_num
    have h3 : ‖Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))‖ = Real.exp 15 := by
      rw [Complex.norm_exp]; simp; norm_num
    have h1 : ‖Complex.exp (5 + Complex.I*(Δ:ℂ))‖ = Real.exp 5 := by
      rw [Complex.norm_exp]; simp
    calc ‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ))) - Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))
          - Complex.exp (5 + Complex.I*(Δ:ℂ)) + 1‖
        ≤ ‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ))) - Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))
            - Complex.exp (5 + Complex.I*(Δ:ℂ))‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ))) - Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))‖
            + ‖Complex.exp (5 + Complex.I*(Δ:ℂ))‖) + 1 := by
          rw [norm_one]; gcongr; exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ)))‖ + ‖Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))‖)
            + ‖Complex.exp (5 + Complex.I*(Δ:ℂ))‖) + 1 := by
          gcongr; exact norm_sub_le _ _
      _ = Real.exp 20 + Real.exp 15 + Real.exp 5 + 1 := by rw [h4, h3, h1]
  have hD : ‖(5 + Complex.I*(Δ:ℂ))^2‖ = 25 + Δ^2 := by
    rw [pow_two, norm_mul, ← sq, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  rw [norm_mul, norm_mul, norm_div, hA, hB, hD]
  calc X^5 * Real.exp (-5) *
        (‖Complex.exp (4*(5 + Complex.I*(Δ:ℂ))) - Complex.exp (3*(5 + Complex.I*(Δ:ℂ)))
          - Complex.exp (5 + Complex.I*(Δ:ℂ)) + 1‖ / (25+Δ^2))
      ≤ X^5 * Real.exp (-5) * ((Real.exp 20 + Real.exp 15 + Real.exp 5 + 1) / (25+Δ^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right hC (by positivity)
    _ ≤ X^5 * Real.exp (-5) * ((Real.exp 20 + Real.exp 15 + Real.exp 5 + 1) / (1+Δ^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [sq_nonneg Δ])
    _ ≤ X^5 * Real.exp (-4) * ((Real.exp 20 + Real.exp 15 + Real.exp 5 + 1) / (1+Δ^2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by norm_num)
    _ = Real.exp (-4)*(1+Real.exp 5+Real.exp 20+Real.exp 15)*X^5/(1+Δ^2) := by ring

end Work.BMF
