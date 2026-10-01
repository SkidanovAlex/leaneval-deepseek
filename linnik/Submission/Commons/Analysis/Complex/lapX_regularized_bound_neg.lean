import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral
open scoped Real Topology

set_option autoImplicit false

noncomputable section

/-!
# Regularized Laplace-transform bound on `[0, x₀]`, for `Re z < 0`.

For `f` continuous on `[0,x₀]`, `C²` on `(0,x₀)`, `‖f''‖ ≤ B` there, vanishing for
`t ≥ x₀`, and any `z` with `Re z < 0`, we bound the regularized transform
`∫₀^{x₀} e^{-zt} f(t) dt - f(0)/z` by `O(1/|z|²)`, with the exponential growth
`e^{-Re z · x₀}` made explicit.

The proof uses the regularizing kernel `lapKernel` (a solution of `Φ'' = e^{-zt}`
vanishing at both endpoints); double integration by parts transposes both
derivatives onto `f`, leaving no need to control `f'` at the endpoints. -/

private def lapExp (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(z * (t : ℂ)))

private def lapKernel (z : ℂ) (x₀ : ℝ) (t : ℝ) : ℂ :=
  (lapExp z t - 1 + (t : ℂ) * ((1 - lapExp z x₀) / x₀)) / z ^ 2

private def lapKernelDeriv (z : ℂ) (x₀ : ℝ) (t : ℝ) : ℂ :=
  (-z * lapExp z t + (1 - lapExp z x₀) / x₀) / z ^ 2

private def lapH (z : ℂ) (x₀ : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  lapKernelDeriv z x₀ t * f t - lapKernel z x₀ t * deriv f t

/-! ## Basic regularity of the exponential kernel -/

private lemma hasDerivAt_lapExp (z : ℂ) (t : ℝ) :
    HasDerivAt (lapExp z) (-z * lapExp z t) t := by
  unfold lapExp
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => z * (s : ℂ)) (z * 1) t := h1.const_mul z
  have h3 : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-(z * 1)) t := h2.neg
  have h3' : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-z) t := by simpa using h3
  have h4 := h3'.cexp
  convert h4 using 1
  ring

private lemma continuous_lapExp (z : ℂ) : Continuous (lapExp z) := by
  unfold lapExp
  fun_prop

private lemma hasDerivAt_lapKernel (z : ℂ) (x₀ : ℝ) (t : ℝ) :
    HasDerivAt (lapKernel z x₀) (lapKernelDeriv z x₀ t) t := by
  unfold lapKernel lapKernelDeriv
  have h : HasDerivAt (fun s : ℝ => lapExp z s - 1 + (s : ℂ) * ((1 - lapExp z x₀) / x₀))
      (-z * lapExp z t + ((1 - lapExp z x₀) / x₀)) t := by
    apply HasDerivAt.add
    · exact (hasDerivAt_lapExp z t).sub_const 1
    · have hh := (HasDerivAt.ofReal_comp (hasDerivAt_id t)).mul_const ((1 - lapExp z x₀)/x₀)
      simpa using hh
  simpa using h.div_const (z^2)

private lemma hasDerivAt_lapKernelDeriv (z : ℂ) (x₀ : ℝ) {t : ℝ} (hz : z ≠ 0) :
    HasDerivAt (lapKernelDeriv z x₀) (lapExp z t) t := by
  unfold lapKernelDeriv
  have h : HasDerivAt (fun s : ℝ => -z * lapExp z s + (1 - lapExp z x₀)/x₀)
      (-z * (-z * lapExp z t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => -z * lapExp z s) ((-z) * (-z * lapExp z t)) t :=
      (hasDerivAt_lapExp z t).const_mul (-z)
    exact h1.add_const _
  have h2 := h.div_const (z^2)
  have hv : -z * (-z * lapExp z t) / z^2 = lapExp z t := by
    rw [div_eq_iff (pow_ne_zero 2 hz)]
    ring
  rw [hv] at h2
  exact h2

private lemma lapKernel_zero (z : ℂ) (x₀ : ℝ) : lapKernel z x₀ 0 = 0 := by
  unfold lapKernel lapExp
  simp

private lemma lapKernel_x₀ (z : ℂ) {x₀ : ℝ} (hx₀ : (x₀ : ℂ) ≠ 0) :
    lapKernel z x₀ x₀ = 0 := by
  unfold lapKernel
  have hcancel : (x₀ : ℂ) * ((1 - lapExp z x₀) / (x₀ : ℂ)) = 1 - lapExp z x₀ := by
    rw [mul_comm, div_mul_cancel₀ _ hx₀]
  rw [hcancel, show lapExp z x₀ - 1 + (1 - lapExp z x₀) = 0 by ring, zero_div]

private lemma deriv_lapKernel (z : ℂ) (x₀ : ℝ) :
    deriv (lapKernel z x₀) = lapKernelDeriv z x₀ := by
  funext t
  exact (hasDerivAt_lapKernel z x₀ t).deriv

private lemma continuous_lapKernel (z : ℂ) (x₀ : ℝ) : Continuous (lapKernel z x₀) := by
  unfold lapKernel lapExp
  fun_prop

private lemma continuous_lapKernelDeriv (z : ℂ) (x₀ : ℝ) : Continuous (lapKernelDeriv z x₀) := by
  unfold lapKernelDeriv lapExp
  fun_prop

private lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

/-! ## The exponential bound in the `Re z < 0` regime -/

private lemma norm_lapExp_le_exp {z : ℂ} {x₀ t : ℝ} (hz : z.re < 0) (ht : t ≤ x₀) :
    ‖lapExp z t‖ ≤ Real.exp (-z.re * x₀) := by
  rw [lapExp, Complex.norm_exp]
  have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  apply Real.exp_le_exp.mpr
  nlinarith [hz, ht]

private lemma norm_lapKernel_le {x₀ : ℝ} (hx₀ : 0 < x₀) {z : ℂ} (hz : z.re < 0) {t : ℝ}
    (ht : t ∈ Set.Icc 0 x₀) :
    ‖lapKernel z x₀ t‖ ≤ (2 + 2 * t / x₀) * Real.exp (-z.re * x₀) / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn2 : (0:ℝ) < ‖z‖ ^ 2 := by
    have : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    positivity
  have hE1 : (1:ℝ) ≤ Real.exp (-z.re * x₀) := Real.one_le_exp (by nlinarith [hz, hx₀])
  have ht0 : 0 ≤ t := ht.1
  have hE : ‖lapExp z t‖ ≤ Real.exp (-z.re * x₀) := norm_lapExp_le_exp hz ht.2
  have hEx : ‖lapExp z x₀‖ ≤ Real.exp (-z.re * x₀) := norm_lapExp_le_exp hz le_rfl
  have hsub : ‖(1:ℂ) - lapExp z x₀‖ ≤ 1 + Real.exp (-z.re * x₀) := by
    have h := norm_sub_le (1:ℂ) (lapExp z x₀)
    rw [norm_one] at h
    linarith
  have hc : ‖((1 - lapExp z x₀) / (x₀ : ℂ))‖ ≤ (1 + Real.exp (-z.re * x₀)) / x₀ := by
    rw [norm_div, norm_ofReal_complex, abs_of_pos hx₀]
    exact div_le_div_of_nonneg_right hsub (le_of_lt hx₀)
  have htc : ‖(t : ℂ) * ((1 - lapExp z x₀) / x₀)‖ ≤ t * ((1 + Real.exp (-z.re * x₀))/x₀) := by
    rw [norm_mul, norm_ofReal_complex, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left hc ht0
  have hnum : ‖lapExp z t - 1 + (t : ℂ) * ((1 - lapExp z x₀) / x₀)‖
      ≤ (1 + Real.exp (-z.re * x₀)) * (1 + t/x₀) := by
    have h1 : ‖lapExp z t - 1‖ ≤ Real.exp (-z.re * x₀) + 1 := by
      have h := norm_sub_le (lapExp z t) (1:ℂ)
      rw [norm_one] at h
      linarith
    calc ‖lapExp z t - 1 + (t : ℂ) * ((1 - lapExp z x₀) / x₀)‖
        ≤ ‖lapExp z t - 1‖ + ‖(t : ℂ) * ((1 - lapExp z x₀) / x₀)‖ := norm_add_le _ _
      _ ≤ (Real.exp (-z.re * x₀) + 1) + t * ((1 + Real.exp (-z.re * x₀))/x₀) := add_le_add h1 htc
      _ = (1 + Real.exp (-z.re * x₀)) * (1 + t / x₀) := by
          field_simp
          ring
  have hfac : (0:ℝ) ≤ 1 + t / x₀ := by
    have : 0 ≤ t / x₀ := div_nonneg ht0 (le_of_lt hx₀)
    linarith
  have hkey : (1 + Real.exp (-z.re * x₀)) * (1 + t/x₀)
      ≤ (2 + 2*t/x₀) * Real.exp (-z.re * x₀) := by
    have hrw : (2 + 2*t/x₀) * Real.exp (-z.re * x₀)
        = 2 * Real.exp (-z.re * x₀) * (1 + t/x₀) := by ring
    rw [hrw]
    apply mul_le_mul_of_nonneg_right _ hfac
    linarith
  rw [lapKernel, norm_div, norm_pow]
  exact div_le_div_of_nonneg_right (le_trans hnum hkey) (le_of_lt hzn2)

/-! ## ContDiff facts -/

private lemma hasDerivAt_iteratedDeriv_two {x₀ : ℝ} {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {x : ℝ} (hx : x ∈ Set.Ioo 0 x₀) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
  have hca : ContDiffAt ℝ 2 f x := hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)
  have hc1 : ContDiffAt ℝ 1 (deriv f) x := hca.derivWithin (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (deriv f) x := hc1.differentiableAt (by norm_num)
  rw [show iteratedDeriv 2 f x = deriv (deriv f) x by
    rw [show (2:ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  exact hd.hasDerivAt

private lemma continuousAt_iteratedDeriv_two {x₀ : ℝ} {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {x : ℝ} (hx : x ∈ Set.Ioo 0 x₀) :
    ContinuousAt (iteratedDeriv 2 f) x := by
  have hca : ContDiffAt ℝ 2 f x := hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)
  have h1 : ContDiffAt ℝ 1 (deriv f) x := hca.derivWithin (m := 1) (by norm_num)
  have h2 : ContDiffAt ℝ 0 (deriv (deriv f)) x := h1.derivWithin (m := 0) (by norm_num)
  have he : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2:ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  exact h2.continuousAt

private lemma exists_bound_norm_deriv {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∃ C : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv f t‖ ≤ C := by
  refine ⟨‖deriv f (x₀/2)‖ + |B| * x₀, fun t ht => ?_⟩
  have hmid : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hsub : Set.uIcc (x₀/2) t ⊆ Set.Ioo (0:ℝ) x₀ := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨lt_of_lt_of_le hmid.1 h1, lt_of_le_of_lt h2 ht.2⟩
    · exact ⟨lt_of_lt_of_le ht.1 h1, lt_of_le_of_lt h2 hmid.2⟩
  have hcont : ContinuousOn (iteratedDeriv 2 f) (Set.uIcc (x₀/2) t) :=
    fun x hx => (continuousAt_iteratedDeriv_two hf2 (hsub hx)).continuousWithinAt
  have hint : IntervalIntegrable (iteratedDeriv 2 f) volume (x₀/2) t :=
    hcont.intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc (x₀/2) t, HasDerivAt (deriv f) (iteratedDeriv 2 f x) x :=
    fun x hx => hasDerivAt_iteratedDeriv_two hf2 (hsub hx)
  have hFTC : ∫ s in (x₀/2)..t, iteratedDeriv 2 f s = deriv f t - deriv f (x₀/2) :=
    integral_eq_sub_of_hasDerivAt hderiv hint
  have hb : ‖deriv f t - deriv f (x₀/2)‖ ≤ |B| * x₀ := by
    rw [← hFTC]
    rcases le_total (x₀/2) t with hle | hle
    · calc ‖∫ s in (x₀/2)..t, iteratedDeriv 2 f s‖
          ≤ ∫ s in (x₀/2)..t, ‖iteratedDeriv 2 f s‖ := norm_integral_le_integral_norm hle
        _ ≤ ∫ s in (x₀/2)..t, |B| := by
            refine integral_mono_on_of_le_Ioo hle (hcont.norm.intervalIntegrable) ?_ (fun s hs => ?_)
            · exact intervalIntegrable_const
            · have hs' : s ∈ Set.Ioo (0:ℝ) x₀ := ⟨lt_trans hmid.1 hs.1, lt_trans hs.2 ht.2⟩
              exact le_trans (hBnd s hs') (le_abs_self B)
        _ = (t - x₀/2) * |B| := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
        _ ≤ |B| * x₀ := by
            have : t - x₀/2 ≤ x₀ := by linarith [ht.2]
            nlinarith [abs_nonneg B]
    · rw [intervalIntegral.integral_symm, norm_neg]
      calc ‖∫ s in t..(x₀/2), iteratedDeriv 2 f s‖
          ≤ ∫ s in t..(x₀/2), ‖iteratedDeriv 2 f s‖ := norm_integral_le_integral_norm hle
        _ ≤ ∫ s in t..(x₀/2), |B| := by
            refine integral_mono_on_of_le_Ioo hle (hcont.norm.intervalIntegrable).symm ?_ (fun s hs => ?_)
            · exact intervalIntegrable_const
            · have hs' : s ∈ Set.Ioo (0:ℝ) x₀ := ⟨lt_trans ht.1 hs.1, lt_trans hs.2 hmid.2⟩
              exact le_trans (hBnd s hs') (le_abs_self B)
        _ = (x₀/2 - t) * |B| := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
        _ ≤ |B| * x₀ := by
            have : x₀/2 - t ≤ x₀ := by linarith [ht.1, hx₀]
            nlinarith [abs_nonneg B]
  calc ‖deriv f t‖ = ‖(deriv f t - deriv f (x₀/2)) + deriv f (x₀/2)‖ := by
        congr 1
        ring
    _ ≤ ‖deriv f t - deriv f (x₀/2)‖ + ‖deriv f (x₀/2)‖ := norm_add_le _ _
    _ ≤ |B| * x₀ + ‖deriv f (x₀/2)‖ := by linarith
    _ = ‖deriv f (x₀/2)‖ + |B| * x₀ := by ring

private lemma integral_linear_bound {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∫ t in (0:ℝ)..x₀, (2 + 2 * t / x₀)) = 3 * x₀ := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) x₀,
      HasDerivAt (fun s : ℝ => 2*s + s^2/x₀) (2 + 2*t/x₀) t := by
    intro t ht
    apply HasDerivAt.add
    · simpa using (hasDerivAt_id (𝕜:=ℝ) t).const_mul 2
    · have h := (hasDerivAt_id (𝕜 := ℝ) t).pow 2
      simpa using h.div_const x₀
  have hint : IntervalIntegrable (fun t : ℝ => 2 + 2 * t / x₀) volume 0 x₀ :=
    (by fun_prop : Continuous (fun t : ℝ => 2 + 2*t/x₀)).intervalIntegrable 0 x₀
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have hv : (fun s : ℝ => 2*s + s^2/x₀) x₀ - (fun s : ℝ => 2*s + s^2/x₀) 0 = 3 * x₀ := by
    have hx₀ne : x₀ ≠ 0 := hx₀.ne'
    show 2 * x₀ + x₀ ^ 2 / x₀ - (2 * 0 + 0 ^ 2 / x₀) = 3 * x₀
    rw [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, mul_zero, add_zero, sub_zero]
    field_simp
    ring
  rw [hv]

private lemma integral_norm_lapKernel_le {x₀ : ℝ} (hx₀ : 0 < x₀) {z : ℂ} (hz : z.re < 0) :
    (∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t‖) ≤ 3 * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2 := by
  have hcont1 : Continuous (fun t : ℝ => ‖lapKernel z x₀ t‖) := (continuous_lapKernel z x₀).norm
  have hint1 : IntervalIntegrable (fun t : ℝ => ‖lapKernel z x₀ t‖) volume 0 x₀ :=
    hcont1.intervalIntegrable 0 x₀
  have hcont2 : Continuous (fun t : ℝ => (2 + 2*t/x₀) * Real.exp (-z.re * x₀) / ‖z‖^2) := by
    apply Continuous.div_const
    exact Continuous.mul (by fun_prop) continuous_const
  have hint2 : IntervalIntegrable (fun t : ℝ => (2 + 2*t/x₀) * Real.exp (-z.re * x₀) / ‖z‖^2)
      volume 0 x₀ := hcont2.intervalIntegrable 0 x₀
  have hmono := integral_mono_on_of_le_Ioo hx₀.le hint1 hint2
      (fun t ht => norm_lapKernel_le hx₀ hz ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hval : (∫ t in (0:ℝ)..x₀, (2 + 2*t/x₀) * Real.exp (-z.re * x₀) / ‖z‖^2)
      = 3 * x₀ * Real.exp (-z.re * x₀) / ‖z‖^2 := by
    rw [show (fun t : ℝ => (2 + 2*t/x₀) * Real.exp (-z.re * x₀) / ‖z‖^2)
        = fun t => (Real.exp (-z.re * x₀) / ‖z‖^2) * (2 + 2*t/x₀) by funext t; ring]
    rw [intervalIntegral.integral_const_mul, integral_linear_bound hx₀]
    ring
  linarith [hmono, hval]

/-! ## Integrability of the second-derivative kernel term -/

private lemma continuousOn_iteratedDeriv_two {x₀ : ℝ} {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) :
    ContinuousOn (iteratedDeriv 2 f) (Set.Ioo 0 x₀) :=
  fun _x hx => (continuousAt_iteratedDeriv_two hf2 hx).continuousWithinAt

private lemma intervalIntegrable_kernel_mul {x₀ B : ℝ} (hx₀ : 0 < x₀) {z : ℂ} (hz : z.re < 0)
    {f : ℝ → ℂ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    IntervalIntegrable (fun t => lapKernel z x₀ t * iteratedDeriv 2 f t) volume 0 x₀ := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn2 : (0:ℝ) < ‖z‖ ^ 2 := by
    have : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    positivity
  have hEpos : (0:ℝ) < Real.exp (-z.re * x₀) := Real.exp_pos _
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
  · refine IntegrableOn.of_bound ?_ ?_ ((4 * Real.exp (-z.re * x₀)/‖z‖^2) * |B|) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (continuous_lapKernel z x₀).continuousOn.mul
        ((continuousOn_iteratedDeriv_two hf2)) |>.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have htIcc : t ∈ Set.Icc (0:ℝ) x₀ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hb1 : ‖lapKernel z x₀ t‖ ≤ 4 * Real.exp (-z.re * x₀)/‖z‖^2 := by
        refine le_trans (norm_lapKernel_le hx₀ hz htIcc) ?_
        apply div_le_div_of_nonneg_right _ (le_of_lt hzn2)
        have h2 : 2 + 2 * t / x₀ ≤ 4 := by
          have ht1 : t / x₀ ≤ 1 := by rw [div_le_iff₀ hx₀]; linarith [htIcc.2]
          rw [mul_div_assoc]; linarith
        exact mul_le_mul_of_nonneg_right h2 hEpos.le
      calc ‖lapKernel z x₀ t * iteratedDeriv 2 f t‖
          = ‖lapKernel z x₀ t‖ * ‖iteratedDeriv 2 f t‖ := norm_mul _ _
        _ ≤ (4 * Real.exp (-z.re * x₀)/‖z‖^2) * |B| :=
            mul_le_mul hb1 (le_trans (hBnd t ht) (le_abs_self B)) (norm_nonneg _) (by positivity)

/-! ## The regularized Laplace-transform bound -/

theorem lapX_regularized_bound_neg {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {z : ℂ} (hz : z.re < 0) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
      ≤ (3 * B * x₀ * Real.exp (-z.re * x₀) + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀) / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hx₀ne : (x₀ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]; exact hx₀.ne'
  have hfx₀ : f x₀ = 0 := hvan x₀ le_rfl
  obtain ⟨C, hC⟩ := exists_bound_norm_deriv hx₀ hf2 hBnd
  have hH_deriv : ∀ x ∈ Set.Ioo (0:ℝ) x₀,
      HasDerivAt (lapH z x₀ f)
        (lapExp z x * f x - lapKernel z x₀ x * iteratedDeriv 2 f x) x := by
    intro x hx
    have hKd : HasDerivAt (lapKernelDeriv z x₀) (lapExp z x) x :=
      hasDerivAt_lapKernelDeriv z x₀ hz0
    have hK : HasDerivAt (lapKernel z x₀) (lapKernelDeriv z x₀ x) x :=
      hasDerivAt_lapKernel z x₀ x
    have hf' : HasDerivAt f (deriv f x) x :=
      (hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num) |>.hasDerivAt
    have hf'' : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := hasDerivAt_iteratedDeriv_two hf2 hx
    have h3 : HasDerivAt
        (fun t => lapKernelDeriv z x₀ t * f t - lapKernel z x₀ t * deriv f t)
        ((lapExp z x * f x + lapKernelDeriv z x₀ x * deriv f x)
          - (lapKernelDeriv z x₀ x * deriv f x + lapKernel z x₀ x * iteratedDeriv 2 f x)) x :=
      (hKd.mul hf').sub (hK.mul hf'')
    have hval : (lapExp z x * f x + lapKernelDeriv z x₀ x * deriv f x)
          - (lapKernelDeriv z x₀ x * deriv f x + lapKernel z x₀ x * iteratedDeriv 2 f x)
        = lapExp z x * f x - lapKernel z x₀ x * iteratedDeriv 2 f x := by ring
    unfold lapH
    exact h3.congr_deriv hval
  have hIntA : IntervalIntegrable (fun t : ℝ => lapExp z t * f t) volume 0 x₀ := by
    have hc1 : ContinuousOn (lapExp z) (Set.uIcc (0:ℝ) x₀) := (continuous_lapExp z).continuousOn
    have hc2 : ContinuousOn f (Set.uIcc (0:ℝ) x₀) := by
      rw [Set.uIcc_of_le hx₀.le]; exact hcont
    exact (hc1.mul hc2).intervalIntegrable
  have hIntB : IntervalIntegrable (fun t : ℝ => lapKernel z x₀ t * iteratedDeriv 2 f t) volume 0 x₀ :=
    intervalIntegrable_kernel_mul hx₀ hz hf2 hBnd
  have hint : IntervalIntegrable (fun t : ℝ =>
      lapExp z t * f t - lapKernel z x₀ t * iteratedDeriv 2 f t) volume 0 x₀ :=
    hIntA.sub hIntB
  have ht0 : Filter.Tendsto (lapH z x₀ f) (𝓝[>] (0:ℝ)) (𝓝 (lapKernelDeriv z x₀ 0 * f 0)) := by
    have h1 : Filter.Tendsto (fun t : ℝ => lapKernelDeriv z x₀ t * f t) (𝓝[>] (0:ℝ))
        (𝓝 (lapKernelDeriv z x₀ 0 * f 0)) := by
      have hdK : Filter.Tendsto (lapKernelDeriv z x₀) (𝓝[>] (0:ℝ)) (𝓝 (lapKernelDeriv z x₀ 0)) :=
        (continuous_lapKernelDeriv z x₀).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      have hf0t : Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) :=
        (hcont.continuousWithinAt ⟨le_rfl, le_of_lt hx₀⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hx₀)
      exact hdK.mul hf0t
    have h2 : Filter.Tendsto (fun t : ℝ => lapKernel z x₀ t * deriv f t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hK0 : Filter.Tendsto (lapKernel z x₀) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h := ((continuous_lapKernel z x₀).continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        rwa [lapKernel_zero] at h
      have hbdd : Filter.IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (fun t => ‖deriv f t‖) := by
        refine Filter.isBoundedUnder_of_eventually_le (a := C) ?_
        rw [eventually_nhdsWithin_iff]
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hx₀] with t ht hgt
        exact hC t ⟨hgt, ht⟩
      exact Filter.Tendsto.zero_mul_isBoundedUnder_le hK0 hbdd
    have h := h1.sub h2
    rw [sub_zero] at h
    unfold lapH
    exact h
  have htx₀ : Filter.Tendsto (lapH z x₀ f) (𝓝[<] x₀) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => lapKernelDeriv z x₀ t * f t) (𝓝[<] x₀) (𝓝 0) := by
      have hdK : Filter.Tendsto (lapKernelDeriv z x₀) (𝓝[<] x₀) (𝓝 (lapKernelDeriv z x₀ x₀)) :=
        (continuous_lapKernelDeriv z x₀).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio x₀))
      have hfx : Filter.Tendsto f (𝓝[<] x₀) (𝓝 (f x₀)) :=
        (hcont.continuousWithinAt ⟨le_of_lt hx₀, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hx₀)
      have h := hdK.mul hfx
      rwa [hfx₀, mul_zero] at h
    have h2 : Filter.Tendsto (fun t : ℝ => lapKernel z x₀ t * deriv f t) (𝓝[<] x₀) (𝓝 0) := by
      have hKx : Filter.Tendsto (lapKernel z x₀) (𝓝[<] x₀) (𝓝 0) := by
        have h := ((continuous_lapKernel z x₀).continuousAt (x := x₀)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio x₀))
        rwa [lapKernel_x₀ z hx₀ne] at h
      have hbdd : Filter.IsBoundedUnder (· ≤ ·) (𝓝[<] x₀) (fun t => ‖deriv f t‖) := by
        refine Filter.isBoundedUnder_of_eventually_le (a := C) ?_
        rw [eventually_nhdsWithin_iff]
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx₀] with t ht hgt
        exact hC t ⟨ht, hgt⟩
      exact Filter.Tendsto.zero_mul_isBoundedUnder_le hKx hbdd
    have h := h1.sub h2
    rw [sub_zero] at h
    unfold lapH
    exact h
  have hFTC := integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hH_deriv hint ht0 htx₀
  have hsub : (∫ t in (0:ℝ)..x₀, (lapExp z t * f t - lapKernel z x₀ t * iteratedDeriv 2 f t))
      = (∫ t in (0:ℝ)..x₀, lapExp z t * f t)
        - (∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t) :=
    intervalIntegral.integral_sub hIntA hIntB
  rw [hsub] at hFTC
  have hid : (∫ t in (0:ℝ)..x₀, lapExp z t * f t)
      = (∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)
        - lapKernelDeriv z x₀ 0 * f 0 := by
    rw [zero_sub] at hFTC
    have h1 := sub_eq_iff_eq_add.mp hFTC
    rw [h1]; ring
  have hcorr : lapKernelDeriv z x₀ 0 + 1 / z = (1 - lapExp z x₀) / (x₀ * z ^ 2) := by
    unfold lapKernelDeriv
    rw [show lapExp z 0 = 1 by simp [lapExp]]
    field_simp
    ring
  have hcorrb : ‖lapKernelDeriv z x₀ 0 + 1 / z‖
      ≤ (Real.exp (-z.re * x₀) + 1) / (x₀ * ‖z‖ ^ 2) := by
    rw [hcorr, norm_div, norm_mul, norm_pow, norm_ofReal_complex, abs_of_pos hx₀]
    have hEsub : ‖(1:ℂ) - lapExp z x₀‖ ≤ Real.exp (-z.re * x₀) + 1 := by
      have h := norm_sub_le (1:ℂ) (lapExp z x₀)
      rw [norm_one] at h
      have hEx : ‖lapExp z x₀‖ ≤ Real.exp (-z.re * x₀) := norm_lapExp_le_exp hz le_rfl
      linarith
    exact div_le_div_of_nonneg_right hEsub (by positivity)
  have hIntK : IntervalIntegrable (fun t : ℝ => ‖lapKernel z x₀ t‖) volume 0 x₀ :=
    (continuous_lapKernel z x₀).norm.intervalIntegrable 0 x₀
  have hIntKle : (∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t‖)
      ≤ 3 * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2 := integral_norm_lapKernel_le hx₀ hz
  have hIntBnd : ‖(∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)‖
      ≤ 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2 := by
    have hInt1 : IntervalIntegrable (fun t : ℝ => ‖lapKernel z x₀ t‖ * ‖iteratedDeriv 2 f t‖)
        volume 0 x₀ := by simpa only [norm_mul] using hIntB.norm
    have hInt2 : IntervalIntegrable (fun t : ℝ => ‖lapKernel z x₀ t‖ * B) volume 0 x₀ :=
      hIntK.mul_const B
    calc ‖∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t‖
        ≤ ∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t * iteratedDeriv 2 f t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx₀.le
      _ = ∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t‖ * ‖iteratedDeriv 2 f t‖ := by
          exact intervalIntegral.integral_congr (fun t _ => norm_mul _ _)
      _ ≤ ∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t‖ * B := by
          refine integral_mono_on_of_le_Ioo hx₀.le hInt1 hInt2 (fun t ht => ?_)
          exact mul_le_mul_of_nonneg_left (hBnd t ht) (norm_nonneg _)
      _ = B * (∫ t in (0:ℝ)..x₀, ‖lapKernel z x₀ t‖) := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ ≤ B * (3 * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hIntKle hB
      _ = 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2 := by ring
  have hA : (∫ t in (0:ℝ)..x₀, lapExp z t * f t) - f 0 / z
      = (∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)
        - f 0 * (lapKernelDeriv z x₀ 0 + 1 / z) := by
    rw [hid]; ring
  have hmain : ‖(∫ t in (0:ℝ)..x₀, lapExp z t * f t) - f 0 / z‖
      ≤ (3 * B * x₀ * Real.exp (-z.re * x₀) + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀)
        / ‖z‖ ^ 2 := by
    rw [hA]
    calc ‖(∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)
            - f 0 * (lapKernelDeriv z x₀ 0 + 1 / z)‖
        ≤ ‖(∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)‖
            + ‖f 0 * (lapKernelDeriv z x₀ 0 + 1 / z)‖ := norm_sub_le _ _
      _ = ‖(∫ t in (0:ℝ)..x₀, lapKernel z x₀ t * iteratedDeriv 2 f t)‖
            + ‖f 0‖ * ‖lapKernelDeriv z x₀ 0 + 1 / z‖ := by rw [norm_mul]
      _ ≤ 3 * B * x₀ * Real.exp (-z.re * x₀) / ‖z‖ ^ 2
            + ‖f 0‖ * ((Real.exp (-z.re * x₀) + 1) / (x₀ * ‖z‖ ^ 2)) :=
          add_le_add hIntBnd (mul_le_mul_of_nonneg_left hcorrb (norm_nonneg (f 0)))
      _ = (3 * B * x₀ * Real.exp (-z.re * x₀) + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀)
            / ‖z‖ ^ 2 := by
          have hzn : ‖z‖ ^ 2 ≠ 0 := by positivity
          field_simp [hzn, hx₀.ne']
  simpa only [lapExp] using hmain

end

end Commons.Analysis.Complex