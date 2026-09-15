import Mathlib
import Submission.Commons.Analysis.Integral.uScaleHalf_integrable
import Submission.Commons.Analysis.Integral.integrable_log_lorentz
import Submission.Commons.NumberTheory.Zeta.zeta_region_inv_analytic_bound_ne

namespace Commons.NumberTheory.Zeta

open MeasureTheory

noncomputable section

/-- Componentwise product bound for seven nonnegative factors. -/
private lemma mul_seven_le {a a' b b' c c' d d' e e' s s' u u' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d') (he : e ≤ e')
    (hs : s ≤ s') (hu : u ≤ u')
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (he0 : 0 ≤ e)
    (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (ha0' : 0 ≤ a') (hb0' : 0 ≤ b') (hc0' : 0 ≤ c') (hd0' : 0 ≤ d') (he0' : 0 ≤ e')
    (hs0' : 0 ≤ s') (_hu0' : 0 ≤ u') :
    a * b * c * d * e * s * u ≤ a' * b' * c' * d' * e' * s' * u' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha0'
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha0' hb0')
  have h3 : a * b * c * d ≤ a' * b' * c' * d' :=
    mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha0' hb0') hc0')
  have h4 : a * b * c * d * e ≤ a' * b' * c' * d' * e' :=
    mul_le_mul h3 he he0 (mul_nonneg (mul_nonneg (mul_nonneg ha0' hb0') hc0') hd0')
  have h5 : a * b * c * d * e * s ≤ a' * b' * c' * d' * e' * s' :=
    mul_le_mul h4 hs hs0
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0' hb0') hc0') hd0') he0')
  exact mul_le_mul h5 hu hu0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0' hb0') hc0') hd0') he0') hs0')

private lemma greenTao_eta_sigma_norm_le {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) (f : ℂ → ℂ → ℂ)
    (B C₁ C₂ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        + ((1 : ℂ) + (t' : ℂ) * Complex.I))‖ ≤ C₂)
    (t t' : ℝ) :
    ‖f (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I))
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2
            * (((1 : ℂ) + (t' : ℂ) * Complex.I)) ^ 2)‖
      ≤ (B * C₂ * C₁ * C₁ * R ^ 2)
        * ((Real.log (|t| + 2) + 1) / ((1 / Real.log R) ^ 2 + t ^ 2))
        * ((Real.log (|t'| + 2) + 1) / (1 + t' ^ 2)) := by
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogR1 : 1 ≤ Real.log R := by
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
    exact le_trans h3 (Real.log_le_log (by norm_num) hR)
  have hBnn : 0 ≤ B := by
    have h := hbound 1 1 (by
      rw [Complex.one_im, abs_zero, zero_add, Complex.one_re]
      have h0 : 0 ≤ β / Real.log 2 := div_nonneg hβ.le (Real.log_nonneg (by norm_num))
      linarith) (le_refl _) (by
      rw [Complex.one_im, abs_zero, zero_add, Complex.one_re]
      have h0 : 0 ≤ β / Real.log 2 := div_nonneg hβ.le (Real.log_nonneg (by norm_num))
      linarith) (le_refl _)
    exact le_trans (norm_nonneg _) h
  set A : ℝ := 1 / Real.log R with hA
  have hApos : 0 < A := by rw [hA]; exact one_div_pos.mpr hlogR
  have hAle1 : A ≤ 1 := by rw [hA, div_le_one hlogR]; exact hlogR1
  set z : ℂ := (A : ℂ) + (t : ℂ) * Complex.I with hz
  set w : ℂ := (1 : ℂ) + (t' : ℂ) * Complex.I with hw
  have hzre : z.re = A := by rw [hz]; simp
  have hzim : z.im = t := by rw [hz]; simp
  have hwre : w.re = 1 := by rw [hw]; simp
  have hwim : w.im = t' := by rw [hw]; simp
  have hzne : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hzre, Complex.zero_re] at hr
    linarith
  have hwne : w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hwre, Complex.zero_re] at hr
    norm_num at hr
  have hzlow : -(β / Real.log (|z.im| + 2)) ≤ z.re := by
    rw [hzre, hzim]
    have h0 : 0 ≤ β / Real.log (|t| + 2) :=
      div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
    linarith
  have hzup : z.re ≤ 1 := by rw [hzre]; exact hAle1
  have hwlow : -(β / Real.log (|w.im| + 2)) ≤ w.re := by
    rw [hwre, hwim]
    have h0 : 0 ≤ β / Real.log (|t'| + 2) :=
      div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t']))
    linarith
  have hwup : w.re ≤ 1 := by rw [hwre]
  have hf : ‖f z w‖ ≤ B := hbound z w hzlow hzup hwlow hwup
  have hZ : ‖riemannZeta (1 + z + w)‖ ≤ C₂ := by
    have h := hnum t t'
    rw [← hz, ← hw] at h
    exact h
  have hcinv : ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|t| + 2) + 1) := by
    have h := hinvb z hzne hzlow hzup
    rwa [hzim] at h
  have hwinv : ‖(riemannZeta (1 + w))⁻¹‖ ≤ C₁ * (Real.log (|t'| + 2) + 1) := by
    have h := hinvb w hwne hwlow hwup
    rwa [hwim] at h
  have hRc : ‖(R : ℂ) ^ (z + w)‖ ≤ R ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
    have hre : (z + w).re = A + 1 := by rw [Complex.add_re, hzre, hwre]
    rw [hre]
    calc R ^ (A + 1) ≤ R ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = R ^ 2 := by rw [Real.rpow_two]
  have hznorm : ‖z‖ ^ 2 = A ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]; ring
  have hwnorm : ‖w‖ ^ 2 = 1 + t' ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
  have hzinv2 : ‖(z ^ 2)⁻¹‖ = 1 / (A ^ 2 + t ^ 2) := by
    rw [norm_inv, norm_pow, hznorm, one_div]
  have hwinv2 : ‖(w ^ 2)⁻¹‖ = 1 / (1 + t' ^ 2) := by
    rw [norm_inv, norm_pow, hwnorm, one_div]
  have hnorm_eq : ‖f z w * (riemannZeta (1 + z + w)
          / (riemannZeta (1 + z) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2)‖
      = ‖f z w‖ * ‖riemannZeta (1 + z + w)‖ * ‖(riemannZeta (1 + z))⁻¹‖
        * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z + w)‖ * ‖(z ^ 2)⁻¹‖
        * ‖(w ^ 2)⁻¹‖ := by
    rw [show f z w * (riemannZeta (1 + z + w)
            / (riemannZeta (1 + z) * riemannZeta (1 + w)))
          * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2)
        = f z w * riemannZeta (1 + z + w) * (riemannZeta (1 + z))⁻¹
          * (riemannZeta (1 + w))⁻¹ * (R : ℂ) ^ (z + w) * (z ^ 2)⁻¹
          * (w ^ 2)⁻¹ by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]; ring]
    simp only [norm_mul]
  calc ‖f z w * (riemannZeta (1 + z + w)
          / (riemannZeta (1 + z) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2)‖
      = ‖f z w‖ * ‖riemannZeta (1 + z + w)‖ * ‖(riemannZeta (1 + z))⁻¹‖
        * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z + w)‖ * ‖(z ^ 2)⁻¹‖
        * ‖(w ^ 2)⁻¹‖ := hnorm_eq
    _ ≤ B * C₂ * (C₁ * (Real.log (|t| + 2) + 1)) * (C₁ * (Real.log (|t'| + 2) + 1))
          * R ^ 2 * (1 / (A ^ 2 + t ^ 2)) * (1 / (1 + t' ^ 2)) := by
        have hlogt : 0 ≤ Real.log (|t| + 2) + 1 := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
          linarith
        have hlogt' : 0 ≤ Real.log (|t'| + 2) + 1 := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ |t'| + 2 by linarith [abs_nonneg t'])
          linarith
        have h3nn : 0 ≤ C₁ * (Real.log (|t| + 2) + 1) := mul_nonneg hC1.le hlogt
        have h4nn : 0 ≤ C₁ * (Real.log (|t'| + 2) + 1) := mul_nonneg hC1.le hlogt'
        have h600 : 0 ≤ 1 / (A ^ 2 + t ^ 2) := by positivity
        have h700 : 0 ≤ 1 / (1 + t' ^ 2) := by positivity
        exact mul_seven_le hf hZ hcinv hwinv hRc hzinv2.le hwinv2.le
          (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) (norm_nonneg _)
          hBnn hC2.le h3nn h4nn (sq_nonneg R) h600 h700
    _ = (B * C₂ * C₁ * C₁ * R ^ 2)
          * ((Real.log (|t| + 2) + 1) / (A ^ 2 + t ^ 2))
          * ((Real.log (|t'| + 2) + 1) / (1 + t' ^ 2)) := by ring

private lemma greenTao_eta_sigma_continuous_aux {R : ℝ} (hR : 3 ≤ R) (f : ℂ → ℂ → ℂ)
    (hcont : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (fun t t' : ℝ =>
      f (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I))
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2
            * (((1 : ℂ) + (t' : ℂ) * Complex.I)) ^ 2))) := by
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hApos : 0 < 1 / Real.log R := one_div_pos.mpr hlogR
  set A : ℝ := 1 / Real.log R with hA
  set Zc : ℝ × ℝ → ℂ := fun p => (A : ℂ) + (p.1 : ℂ) * Complex.I with hZ
  set Wc : ℝ × ℝ → ℂ := fun p => (1 : ℂ) + (p.2 : ℂ) * Complex.I with hW
  have hZc : Continuous Zc := by rw [hZ]; fun_prop
  have hWc : Continuous Wc := by rw [hW]; fun_prop
  have hZre : ∀ p : ℝ × ℝ, (Zc p).re = A := by intro p; rw [hZ]; simp
  have hWre : ∀ p : ℝ × ℝ, (Wc p).re = 1 := by intro p; rw [hW]; simp
  have hf : Continuous fun p : ℝ × ℝ => f (Zc p) (Wc p) := by
    have h2 : Continuous fun p : ℝ × ℝ => (Zc p, Wc p) := hZc.prodMk hWc
    exact hcont.comp h2
  have harg : Continuous fun p : ℝ × ℝ => (1 : ℂ) + Zc p + Wc p :=
    (continuous_const.add hZc).add hWc
  have hζnum : Continuous fun p : ℝ × ℝ => riemannZeta (1 + Zc p + Wc p) := by
    rw [continuous_iff_continuousAt]
    intro p
    refine ((differentiableAt_riemannZeta ?_).continuousAt).comp harg.continuousAt
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at hre
    rw [hZre p, hWre p] at hre
    linarith
  have hζc : Continuous fun p : ℝ × ℝ => riemannZeta (1 + Zc p) := by
    rw [continuous_iff_continuousAt]
    intro p
    refine ((differentiableAt_riemannZeta ?_).continuousAt).comp
      ((continuous_const.add hZc).continuousAt)
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at hre
    rw [hZre p] at hre
    linarith
  have hζw : Continuous fun p : ℝ × ℝ => riemannZeta (1 + Wc p) := by
    rw [continuous_iff_continuousAt]
    intro p
    refine ((differentiableAt_riemannZeta ?_).continuousAt).comp
      ((continuous_const.add hWc).continuousAt)
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at hre
    rw [hWre p] at hre
    norm_num at hre
  have hratio : Continuous fun p : ℝ × ℝ =>
      riemannZeta (1 + Zc p + Wc p) / (riemannZeta (1 + Zc p) * riemannZeta (1 + Wc p)) := by
    refine hζnum.div (hζc.mul hζw) ?_
    intro p
    refine mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ?_) (riemannZeta_ne_zero_of_one_lt_re ?_)
    · rw [Complex.add_re, Complex.one_re, hZre p]; linarith
    · rw [Complex.add_re, Complex.one_re, hWre p]; norm_num
  have hcpow : Continuous fun p : ℝ × ℝ => (R : ℂ) ^ (Zc p + Wc p) := by
    have hRne : (R : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < R))
    exact (hZc.add hWc).const_cpow (Or.inl hRne)
  have hden : Continuous fun p : ℝ × ℝ => Zc p ^ 2 * Wc p ^ 2 := (hZc.pow 2).mul (hWc.pow 2)
  have hdenne : ∀ p : ℝ × ℝ, Zc p ^ 2 * Wc p ^ 2 ≠ 0 := by
    intro p
    refine mul_ne_zero (pow_ne_zero 2 ?_) (pow_ne_zero 2 ?_)
    · intro h
      have hr := congrArg Complex.re h
      rw [hZre p, Complex.zero_re] at hr
      linarith
    · intro h
      have hr := congrArg Complex.re h
      rw [hWre p, Complex.zero_re] at hr
      norm_num at hr
  have hall : Continuous fun p : ℝ × ℝ =>
      f (Zc p) (Wc p) * (riemannZeta (1 + Zc p + Wc p)
        / (riemannZeta (1 + Zc p) * riemannZeta (1 + Wc p)))
      * (R : ℂ) ^ (Zc p + Wc p) / (Zc p ^ 2 * Wc p ^ 2) :=
    ((hf.mul hratio).mul hcpow).div hden hdenne
  have hgoal : Function.uncurry (fun t t' : ℝ =>
      f ((A : ℂ) + (t : ℂ) * Complex.I) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + ((A : ℂ) + (t : ℂ) * Complex.I)
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + ((A : ℂ) + (t : ℂ) * Complex.I))
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ ((A : ℂ) + (t : ℂ) * Complex.I
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((((A : ℂ) + (t : ℂ) * Complex.I)) ^ 2
            * (((1 : ℂ) + (t' : ℂ) * Complex.I)) ^ 2)) = fun p : ℝ × ℝ =>
      f (Zc p) (Wc p) * (riemannZeta (1 + Zc p + Wc p)
        / (riemannZeta (1 + Zc p) * riemannZeta (1 + Wc p)))
      * (R : ℂ) ^ (Zc p + Wc p) / (Zc p ^ 2 * Wc p ^ 2) := by
    funext p
    simp only [Function.uncurry, hZ, hW]
  rw [hgoal]
  exact hall

/-- The Green-Tao kernel `K R f z z' = f z z' * (ζ(1+z+z')/(ζ(1+z) ζ(1+z')) * R^(z+z')/(z^2 z'^2)`
is jointly integrable on the product of the two vertical lines `Re z = 1/log R` and `Re z' = 1`,
*assuming `f` is continuous*.

Continuity of `f` cannot be dropped: `MeasureTheory.Integrable F μ` unfolds to
`AEStronglyMeasurable F μ ∧ HasFiniteIntegral F μ`, and the pointwise norm bound `hbound` alone
only yields `HasFiniteIntegral` (via domination), never a.e. strong measurability.

Proof route (pointwise domination + product of integrable functions).  Put `A := 1 / log R`
(so `0 < A ≤ 1` because `R ≥ 3 > e`), `z t := A + t·i`, `z' t' := 1 + t'·i`.  Then
`‖f (z t) (z' t')‖ ≤ B`, `‖ζ(1+z t+z' t')‖ ≤ C₂` (`hnum`),
`‖(ζ(1+z t))⁻¹‖ ≤ C₁ (log(|t|+2)+1)` and `‖(ζ(1+z' t'))⁻¹‖ ≤ C₁ (log(|t'|+2)+1)` (`hinvb`, both
points lie in the log-zero-free region: `re z t = A ≤ 1`, `re z' t' = 1`),
`‖R^(z t + z' t')‖ = R^(A+1) ≤ R^2`, `‖(z t)⁻¹‖^2 = 1/(A^2+t^2) ≤ (log R)^2/(1+t^2)` (since
`A^2 + t^2 ≥ A^2 (1+t^2)`), and `‖(z' t')⁻¹‖^2 = 1/(1+t'^2)`.  Hence the integrand `F` satisfies
`‖F t t'‖ ≤ K * ((log(|t|+2)+1)/(1+t^2)) * ((log(|t'|+2)+1)/(1+t'^2))`
with `K := B * C₂ * C₁ * C₁ * R^2 * max ((log R)^2) 1`.  The weight
`t ↦ (log(|t|+2)+1)/(1+t^2)` is integrable: it is dominated by the `uScaleHalf` weight
`(|t|+3)^{1/2} (log(|t|+2)+1)/(1+t^2)` (as `(|t|+3)^{1/2} ≥ 1`), which is integrable by
`Commons.Analysis.Integral.uScaleHalf_integrable`.  Then
`fun p : ℝ × ℝ => K * w p.1 * w p.2` is `Integrable (volume.prod volume)` by `Integrable.mul_prod`
(and `Integrable.const_mul`), and `Integrable.mono'` finishes, using that `F` is
a.e. strongly measurable: `F` is *continuous* because `hcont` holds, `(t,t') ↦ (z t, z' t')` is
continuous, `ζ` is continuous at each of the arguments `1+z t`, `1+z' t'`, `1+z t+z' t'` (their real
parts are `1+A > 1` and `2`, so none is the pole `1`; use `continuousAt_riemannZeta`), and the
denominators are nonvanishing (`ζ` has no zeros on `re > 1`). -/
theorem greenTao_kernel_integrable_eta_sigma_cont {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (f : ℂ → ℂ → ℂ) (B C₁ C₂ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂)
    (hcont : Continuous (Function.uncurry f))
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        + ((1 : ℂ) + (t' : ℂ) * Complex.I))‖ ≤ C₂) :
    MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      f (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I))
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2
            * (((1 : ℂ) + (t' : ℂ) * Complex.I)) ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hApos : 0 < 1 / Real.log R := one_div_pos.mpr hlogR
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (B * C₂ * C₁ * C₁ * R ^ 2)
        * ((Real.log (|p.1| + 2) + 1) / ((1 / Real.log R) ^ 2 + p.1 ^ 2))
        * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hg1 : Integrable (fun t : ℝ => (Real.log (|t| + 2) + 1) / ((1 / Real.log R) ^ 2 + t ^ 2))
        MeasureTheory.volume := by
      have h := Commons.Analysis.Integral.integrable_log_lorentz (1 / Real.log R) 0 hApos
      have hfun : (fun t : ℝ => (Real.log (|t| + 2) + 1) / ((1 / Real.log R) ^ 2 + t ^ 2))
          = (fun t : ℝ => (Real.log (2 + |t|) + 1) / ((1 / Real.log R) ^ 2 + (t - 0) ^ 2)) := by
        funext t
        rw [add_comm 2, sub_zero]
      rw [hfun]
      exact h
    have hg2 : Integrable (fun t : ℝ => (Real.log (|t| + 2) + 1) / (1 + t ^ 2))
        MeasureTheory.volume := by
      have h := Commons.Analysis.Integral.integrable_log_lorentz 1 0 (by norm_num : (0:ℝ) < 1)
      have hfun : (fun t : ℝ => (Real.log (|t| + 2) + 1) / (1 + t ^ 2))
          = (fun t : ℝ => (Real.log (2 + |t|) + 1) / (1 ^ 2 + (t - 0) ^ 2)) := by
        funext t
        rw [add_comm 2, sub_zero, one_pow]
      rw [hfun]
      exact h
    have hm := (hg1.const_mul (B * C₂ * C₁ * C₁ * R ^ 2)).mul_prod hg2
    simpa [mul_assoc] using hm
  have hcont' : Continuous (Function.uncurry (fun t t' : ℝ =>
      f (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I))
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I
              + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2
            * (((1 : ℂ) + (t' : ℂ) * Complex.I)) ^ 2))) :=
    greenTao_eta_sigma_continuous_aux hR f hcont
  refine Integrable.mono' hmaj hcont'.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro p
  exact greenTao_eta_sigma_norm_le hβ hR f B C₁ C₂ hC1 hC2 hinvb hbound hnum p.1 p.2

end

end Commons.NumberTheory.Zeta
