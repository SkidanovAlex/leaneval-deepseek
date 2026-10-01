import Mathlib
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral
open scoped Real Topology

set_option autoImplicit false

noncomputable section

/-! ## Auxiliary calculus and algebra lemmas -/

/-- The second iterated derivative of an affine map `ℝ → ℂ` vanishes. -/
private lemma iteratedDeriv_two_affine (a b : ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a + b * (s : ℂ)) t = 0 := by
  have hd : deriv (fun s : ℝ => a + b * (s : ℂ)) = fun _ => b := by
    funext s
    have h : HasDerivAt (fun s : ℝ => a + b * (s : ℂ)) b s := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp
      have := (h1.const_mul b).add_const a
      simpa using this
    exact h.deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, hd]
  simp

/-- The inclusion `ℝ → ℂ` is `C²`. -/
private lemma contDiff_ofReal' : ContDiff ℝ 2 (fun s : ℝ => (s : ℂ)) := by
  have h : (fun s : ℝ => (s : ℂ)) = ⇑Complex.ofRealCLM := by
    funext s; exact (Complex.ofRealCLM_apply s).symm
  rw [h]; exact Complex.ofRealCLM.contDiff

/-- The affine cutoff `t ↦ max 0 (1 - t/x₀)`. -/
private def lapAff (x₀ t : ℝ) : ℝ := max 0 (1 - t / x₀)

/-- The `f(0)`-regularized version of `f` used to make the kernel bound applicable. -/
private def lapAdj (x₀ : ℝ) (c : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t - c * (lapAff x₀ t : ℂ)

private lemma contDiffOn_lapAff {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContDiffOn ℝ 2 (lapAff x₀) (Set.Ioo 0 x₀) := by
  have h1 : ContDiffOn ℝ 2 (fun t : ℝ => 1 - t/x₀) (Set.Ioo 0 x₀) := by fun_prop
  refine h1.congr (fun t ht => ?_)
  simp only [lapAff]
  rw [max_eq_right (by rw [sub_nonneg, div_le_iff₀ hx₀]; linarith [ht.2])]

/-- On the open interval `(0,x₀)` the regularized function has the same second
iterated derivative as `f`, since it differs from `f` there by an affine function. -/
private lemma iteratedDeriv_lapAdj {x₀ : ℝ} (hx₀ : 0 < x₀) (c : ℂ) {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) x₀) :
    iteratedDeriv 2 (lapAdj x₀ c f) t = iteratedDeriv 2 f t := by
  have hmem : Set.Ioo (0:ℝ) x₀ ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have heq : (lapAdj x₀ c f)
      =ᶠ[𝓝 t] (fun s : ℝ => f s - c * ((1 - s/x₀ : ℝ):ℂ)) := by
    filter_upwards [hmem] with s hs
    simp only [lapAdj, lapAff]
    have : max 0 (1 - s/x₀) = 1 - s/x₀ :=
      max_eq_right (by rw [sub_nonneg, div_le_iff₀ hx₀]; linarith [hs.2])
    rw [this]
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 heq]
  have hca : ContDiffAt ℝ 2 f t := hf2.contDiffAt (Ioo_mem_nhds ht.1 ht.2)
  have hs : ContDiffAt ℝ 2 (fun s : ℝ => (s:ℂ)) t := contDiff_ofReal'.contDiffAt
  have hlin : ContDiffAt ℝ 2 (fun s : ℝ => ((1 - s/x₀ : ℝ):ℂ)) t := by
    have hfun : (fun s : ℝ => ((1 - s/x₀ : ℝ):ℂ)) =
        (fun s : ℝ => (1:ℂ) - (s:ℂ) * (x₀:ℂ)⁻¹) := by
      funext s; push_cast; ring
    rw [hfun]
    exact contDiffAt_const.sub (hs.mul contDiffAt_const)
  have hca2 : ContDiffAt ℝ 2 (fun s : ℝ => c * ((1 - s/x₀ : ℝ):ℂ)) t :=
    ContDiffAt.mul contDiffAt_const hlin
  have hsub := iteratedDeriv_sub (f := f) (g := fun s : ℝ => c * ((1 - s/x₀ : ℝ):ℂ)) hca hca2
  change iteratedDeriv 2 (f - fun s : ℝ => c * ((1 - s/x₀ : ℝ):ℂ)) t = iteratedDeriv 2 f t
  rw [hsub]
  have hz : iteratedDeriv 2 (fun s : ℝ => c * ((1 - s/x₀ : ℝ):ℂ)) t = 0 := by
    have hfun : (fun s : ℝ => c * ((1 - s/x₀ : ℝ):ℂ)) =
        (fun s : ℝ => c + (-(c)*(x₀:ℂ)⁻¹) * (s:ℂ)) := by
      funext s; push_cast; ring
    rw [hfun]; exact iteratedDeriv_two_affine c (-(c)*(x₀:ℂ)⁻¹) t
  rw [hz, sub_zero]

private lemma lapAff_van {x₀ : ℝ} (hx₀ : 0 < x₀) {t : ℝ} (ht : x₀ ≤ t) :
    lapAff x₀ t = 0 := by
  simp only [lapAff]
  rw [max_eq_left]
  rw [sub_nonpos, le_div_iff₀ hx₀]
  linarith

private lemma lapAff_zero {x₀ : ℝ} : lapAff x₀ 0 = 1 := by
  simp [lapAff]

/-- `‖1 - e^{-z x}‖ ≤ 2` in the half-plane `Re z ≥ 0`, `x ≥ 0`. -/
private lemma norm_one_sub_exp_neg_le_two {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖(1:ℂ) - Complex.exp (-(z * (x:ℂ)))‖ ≤ 2 := by
  have h1 : ‖Complex.exp (-(z * (x:ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : (-(z*(x:ℂ))).re = -(z.re * x) := by
      simp [Complex.neg_re, Complex.mul_re]
    rw [hre, Real.exp_le_one_iff]
    nlinarith
  calc ‖(1:ℂ) - Complex.exp (-(z*(x:ℂ)))‖ ≤ ‖(1:ℂ)‖ + ‖Complex.exp (-(z*(x:ℂ)))‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

/-- The exact value of `∫₀^{x₀} e^{-zt} (1 - t/x₀) dt`. -/
private lemma affine_integral {x₀ : ℝ} (hx₀ : 0 < x₀) {z : ℂ} (hz : z ≠ 0) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((1 - t/x₀ : ℝ) : ℂ))
      = 1/z - (1 - Complex.exp (-(z * (x₀ : ℂ)))) / ((x₀:ℂ) * z^2) := by
  have hx0c : (x₀:ℂ) ≠ 0 := by exact_mod_cast hx₀.ne'
  let Phi : ℝ → ℂ := fun t =>
    Complex.exp (-(z * (t:ℂ))) * ((t:ℂ)*z + 1 - (x₀:ℂ)*z) / ((x₀:ℂ) * z^2)
  let PhiD : ℝ → ℂ := fun t => Complex.exp (-(z * (t:ℂ))) * (1 - (t:ℂ)*(x₀:ℂ)⁻¹)
  have hPhiD : ∀ t, PhiD t = Complex.exp (-(z*(t:ℂ))) * ((1 - t/x₀ : ℝ):ℂ) := by
    intro t; simp only [PhiD]; congr 1; push_cast; ring
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) x₀, HasDerivAt Phi (PhiD t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h3 : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-(z * 1)) t :=
      (h1.const_mul z).neg
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(z * (s : ℂ))))
        (Complex.exp (-(z*(t:ℂ))) * (-(z*1))) t := h3.cexp
    have h5 : HasDerivAt (fun s : ℝ => (s:ℂ)*z + 1 - (x₀:ℂ)*z) z t := by
      have := (h1.mul_const z).add_const (1 - (x₀:ℂ)*z)
      simpa using this
    have h6 := h4.mul h5
    have hdiv : Phi = fun s : ℝ =>
        (Complex.exp (-(z * (s:ℂ))) * ((s:ℂ)*z + 1 - (x₀:ℂ)*z)) * (((x₀:ℂ)*z^2)⁻¹) := by
      funext s; simp only [Phi]; ring
    rw [hdiv]
    refine (h6.mul_const _).congr_deriv ?_
    simp only [PhiD]
    field_simp
    ring
  have hint : IntervalIntegrable PhiD volume 0 x₀ := by
    apply Continuous.intervalIntegrable
    simp only [PhiD]; fun_prop
  have hcongr : (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * ((1 - t/x₀ : ℝ):ℂ)) = PhiD := by
    funext t; exact (hPhiD t).symm
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Phi]
  have hz2 : z^2 ≠ 0 := pow_ne_zero 2 hz
  have hxc : (x₀:ℂ)*z^2 ≠ 0 := mul_ne_zero hx0c hz2
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  field_simp
  ring

/-! ## The main theorem -/

/-- The regularized Laplace transform bound: for a continuous `f` on `[0,x₀]`, `C²` on `(0,x₀)` with
`‖f''‖ ≤ B`, vanishing for `t ≥ x₀`, the Laplace transform `∫_0^{x₀} e^{-zt} f` differs from
`f 0 / z` by at most `(3 B x₀ + 2 ‖f 0‖ / x₀) / ‖z‖²` in the half-plane `Re z > 0`.
This is Heath-Brown (1992) (5.3)–(5.4). -/
theorem lapX_sub_inv_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {z : ℂ} (hz : 0 < z.re) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
      ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzpos : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hzn2 : (0:ℝ) < ‖z‖ ^ 2 := by positivity
  -- continuity of the exponential kernel
  have hψcont : Continuous (lapAff x₀) := by
    show Continuous (fun t : ℝ => max 0 (1 - t / x₀)); fun_prop
  have hψcontc : Continuous (fun t : ℝ => ((lapAff x₀ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hψcont
  have hExp : Continuous (fun t : ℝ => Complex.exp (-(z * (t:ℂ)))) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
  -- hypotheses for the regularized function
  have hpadj_cont : ContinuousOn (lapAdj x₀ (f 0) f) (Set.Icc 0 x₀) := by
    show ContinuousOn (fun t => f t - (f 0) * (lapAff x₀ t : ℂ)) (Set.Icc 0 x₀)
    exact hcont.sub (continuousOn_const.mul hψcontc.continuousOn)
  have hofreal_c2 : ContDiffOn ℝ 2 (fun t : ℝ => ((1 - t/x₀ : ℝ):ℂ)) (Set.Ioo 0 x₀) :=
    contDiff_ofReal'.comp_contDiffOn (by fun_prop)
  have hpadj_c2 : ContDiffOn ℝ 2 (lapAdj x₀ (f 0) f) (Set.Ioo 0 x₀) := by
    have h1 : ContDiffOn ℝ 2 (fun t : ℝ => f t - (f 0) * ((1 - t/x₀:ℝ):ℂ))
        (Set.Ioo 0 x₀) := hf2.sub (contDiffOn_const.mul hofreal_c2)
    refine h1.congr (fun t ht => ?_)
    simp only [lapAdj, lapAff]
    rw [max_eq_right (by rw [sub_nonneg, div_le_iff₀ hx₀]; linarith [ht.2])]
  have hpadj_bnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 (lapAdj x₀ (f 0) f) t‖ ≤ B := by
    intro t ht
    rw [iteratedDeriv_lapAdj hx₀ (f 0) hf2 ht]
    exact hBnd t ht
  have hpadj_van : ∀ t : ℝ, x₀ ≤ t → lapAdj x₀ (f 0) f t = 0 := by
    intro t ht
    simp only [lapAdj, lapAff_van hx₀ ht, hvan t ht, Complex.ofReal_zero, mul_zero, sub_zero]
  have hpadj_zero : lapAdj x₀ (f 0) f 0 = 0 := by
    simp only [lapAdj, lapAff_zero, Complex.ofReal_one, mul_one, sub_self]
  -- the bound for the regularized function
  have hgbound : ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t)‖
      ≤ 3 * B * x₀ / ‖z‖ ^ 2 :=
    laplace_transform_bound_complex hx₀ hB hpadj_cont hpadj_c2 hpadj_bnd hpadj_van hpadj_zero hz
  -- integrability
  have hI1 : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t) volume 0 x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀.le]
    exact hExp.continuousOn.mul hpadj_cont
  have hI2 : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ)) volume 0 x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀.le]
    exact hExp.continuousOn.mul hψcontc.continuousOn
  -- splitting `f` into the regularized part plus the affine part
  have hsplit : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t)
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t)
        + (f 0) * (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ)) := by
    rw [show (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t)
        = ∫ t in (0:ℝ)..x₀, (Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t
            + (f 0) * (Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))) from by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [lapAdj]; ring]
    rw [intervalIntegral.integral_add hI1 (hI2.const_mul (f 0)),
        intervalIntegral.integral_const_mul]
  -- exact value of the affine part
  have hpsi_eq : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * ((1 - t/x₀ : ℝ):ℂ)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hx₀.le] at ht
    simp only [lapAff]
    rw [max_eq_right (by rw [sub_nonneg, div_le_iff₀ hx₀]; linarith [ht.2])]
  have hpsi_val : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
      = 1/z - (1 - Complex.exp (-(z*(x₀:ℂ)))) / ((x₀:ℂ) * z^2) := by
    rw [hpsi_eq, affine_integral hx₀ hz0]
  -- bound for the affine correction
  have hden : ‖((x₀:ℂ) * z^2)‖ = x₀ * ‖z‖^2 := by
    rw [norm_mul, norm_pow]
    congr 1
    simp [abs_of_pos hx₀]
  have hX : ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ)) - 1/z‖
      ≤ 2/(x₀*‖z‖^2) := by
    rw [hpsi_val]
    have hsub : (1/z - (1 - Complex.exp (-(z*(x₀:ℂ)))) / ((x₀:ℂ) * z^2)) - 1/z
        = -((1 - Complex.exp (-(z*(x₀:ℂ)))) / ((x₀:ℂ) * z^2)) := by ring
    rw [hsub, norm_neg, norm_div, hden]
    exact div_le_div_of_nonneg_right
      (norm_one_sub_exp_neg_le_two hz.le hx₀.le) (le_of_lt (mul_pos hx₀ hzn2))
  have hterm : ‖(f 0) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
      - 1/z)‖ ≤ ‖f 0‖ * (2/(x₀*‖z‖^2)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hX (norm_nonneg _)
  -- the main algebraic identity
  have hmain_eq : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * f t) - f 0 / z
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t)
        + (f 0) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
            - 1/z) := by
    rw [hsplit]; ring
  calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
      = ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t)
          + (f 0) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
              - 1/z)‖ := by rw [hmain_eq]
    _ ≤ ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * lapAdj x₀ (f 0) f t)‖
          + ‖(f 0) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(z*(t:ℂ))) * (lapAff x₀ t : ℂ))
              - 1/z)‖ := norm_add_le _ _
    _ ≤ 3 * B * x₀ / ‖z‖ ^ 2 + ‖f 0‖ * (2/(x₀*‖z‖^2)) := add_le_add hgbound hterm
    _ = (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := by
        have hx0ne : x₀ ≠ 0 := hx₀.ne'
        have hz2ne : ‖z‖^2 ≠ 0 := ne_of_gt hzn2
        field_simp

end

end Commons.Analysis.Complex
