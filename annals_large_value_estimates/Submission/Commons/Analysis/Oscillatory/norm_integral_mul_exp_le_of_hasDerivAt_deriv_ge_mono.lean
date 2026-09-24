import Mathlib
import Submission.Commons.Analysis.Oscillatory.poly_first_derivative_test

namespace Commons.Analysis.Oscillatory

open MeasureTheory Set
open scoped Real Interval

theorem norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono {a b lam : ℝ} (hab : a ≤ b)
    (hlam : 0 < lam) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc a b) ∨ AntitoneOn (deriv φ) (Set.Icc a b))
    (hbound : ∀ t ∈ Set.Icc a b, lam ≤ |deriv φ t|)
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Icc a b)) (hgd : ContinuousOn (deriv g) (Set.Icc a b))
    (hg : ∀ t ∈ Set.Ioo a b, HasDerivAt g (deriv g t) t) :
    ‖(∫ t in a..b, (g t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ)))‖
      ≤ 4 * (|g a| + ∫ t in a..b, |deriv g t|) / lam := by
  set f : ℝ → ℂ := fun t => Complex.exp (Complex.I * (φ t : ℂ)) with hf
  have hfcont : Continuous f := by
    rw [hf]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hφ.continuous))
  set v : ℝ → ℂ := fun x => ∫ t in b..x, f t with hv
  have hvcont : Continuous v := by
    rw [hv]
    exact intervalIntegral.continuous_primitive (fun a b => hfcont.intervalIntegrable a b) b
  have hvderiv : ∀ x, HasDerivAt v (f x) x := by
    intro x
    have h := intervalIntegral.integral_hasDerivAt_right (a := b) (b := x)
      (hfcont.intervalIntegrable b x) (hfcont.stronglyMeasurableAtFilter volume (nhds x))
      hfcont.continuousAt
    rw [hv]
    exact h
  -- pointwise bound on the antiderivative
  have hv_bound : ∀ x ∈ Set.Icc a b, ‖v x‖ ≤ 4 / lam := by
    intro x hx
    have hxb : x ≤ b := hx.2
    have hvx : v x = -∫ t in x..b, f t := by
      change (∫ t in b..x, f t) = -∫ t in x..b, f t
      rw [intervalIntegral.integral_symm (f := f) x b]
    rw [hvx, norm_neg]
    have hmono' : MonotoneOn (deriv φ) (Set.Icc x b) ∨ AntitoneOn (deriv φ) (Set.Icc x b) := by
      rcases hmono with h | h
      · exact Or.inl (h.mono (Set.Icc_subset_Icc hx.1 le_rfl))
      · exact Or.inr (h.mono (Set.Icc_subset_Icc hx.1 le_rfl))
    have hbound' : ∀ t ∈ Set.Icc x b, lam ≤ |deriv φ t| :=
      fun t ht => hbound t ⟨le_trans hx.1 ht.1, ht.2⟩
    simpa [hf] using vdc_first_deriv hxb hlam hφ hmono' hbound'
  have hvb : v b = 0 := by
    change (∫ t in b..b, f t) = 0
    simp
  -- continuity of g as a complex-valued function
  have hu_cont : ContinuousOn (fun t => (g t : ℂ)) [[a, b]] := by
    rw [Set.uIcc_of_le hab]
    simpa [Function.comp_def] using Complex.continuous_ofReal.comp_continuousOn hgc
  have hv_cont : ContinuousOn v [[a, b]] := hvcont.continuousOn.mono (Set.subset_univ _)
  -- derivatives
  have huu' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun t => (g t : ℂ)) ((deriv g x : ℝ) : ℂ) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact (hg x hx).ofReal_comp
  have hvv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (f x) x :=
    fun x _ => hvderiv x
  -- integrability of the derivatives
  have hu'_int : IntervalIntegrable (fun x => ((deriv g x : ℝ) : ℂ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    simpa [Function.comp_def] using Complex.continuous_ofReal.comp_continuousOn hgd
  have hv'_int : IntervalIntegrable (fun x => f x) volume a b := hfcont.intervalIntegrable a b
  -- integration by parts
  have hibp : ∫ t in a..b, (g t : ℂ) * f t
      = (g b : ℂ) * v b - (g a : ℂ) * v a - ∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := fun t => (g t : ℂ))
      (v := v) (u' := fun t => ((deriv g t : ℝ) : ℂ)) (v' := f)
      hu_cont hv_cont huu' hvv' hu'_int hv'_int
  have hkey : ∫ t in a..b, (g t : ℂ) * f t
      = -((g a : ℂ) * v a) - ∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t := by
    rw [hibp, hvb, mul_zero, zero_sub]
  -- bound the remainder integral
  have hInt_bound : ‖∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t‖
      ≤ (4 / lam) * ∫ t in a..b, |deriv g t| := by
    have hbnd : IntervalIntegrable (fun t => (4 / lam) * |deriv g t|) volume a b := by
      have h1 : IntervalIntegrable (deriv g) volume a b := by
        apply ContinuousOn.intervalIntegrable
        rwa [Set.uIcc_of_le hab]
      exact (h1.abs).const_mul (4 / lam)
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := fun t => ((deriv g t : ℝ) : ℂ) * v t)
      (g := fun t => (4 / lam) * |deriv g t|)
      (Filter.Eventually.of_forall (fun t ht => by
        have ht' : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
        have hn : ‖((deriv g t : ℝ) : ℂ)‖ = |deriv g t| := by simp
        rw [norm_mul, hn]
        calc |deriv g t| * ‖v t‖ ≤ |deriv g t| * (4 / lam) :=
              mul_le_mul_of_nonneg_left (hv_bound t ht') (abs_nonneg _)
          _ = (4 / lam) * |deriv g t| := by ring))
      hbnd
    rwa [intervalIntegral.integral_const_mul] at hle
  -- assembly
  have hfinal : ‖∫ t in a..b, (g t : ℂ) * f t‖
      ≤ (4 / lam) * (|g a| + ∫ t in a..b, |deriv g t|) := by
    rw [hkey]
    have hstep1 : ‖-((g a : ℂ) * v a) - ∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t‖
        ≤ ‖(g a : ℂ) * v a‖ + ‖∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t‖ := by
      have heq : -((g a : ℂ) * v a) - ∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t
          = -(((g a : ℂ) * v a) + ∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t) := by ring
      rw [heq, norm_neg]
      exact norm_add_le _ _
    have h2 : ‖(g a : ℂ) * v a‖ ≤ |g a| * (4 / lam) := by
      have hn : ‖((g a : ℝ) : ℂ)‖ = |g a| := by simp
      rw [norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (hv_bound a ⟨le_rfl, hab⟩) (abs_nonneg _)
    have hsum : ‖(g a : ℂ) * v a‖ + ‖∫ t in a..b, ((deriv g t : ℝ) : ℂ) * v t‖
        ≤ (4 / lam) * (|g a| + ∫ t in a..b, |deriv g t|) := by
      refine le_trans (add_le_add h2 hInt_bound) (le_of_eq ?_)
      ring
    exact hstep1.trans hsum
  have hgoal : (4 / lam) * (|g a| + ∫ t in a..b, |deriv g t|)
      = 4 * (|g a| + ∫ t in a..b, |deriv g t|) / lam := by ring
  simpa [hf, hgoal] using hfinal

end Commons.Analysis.Oscillatory
