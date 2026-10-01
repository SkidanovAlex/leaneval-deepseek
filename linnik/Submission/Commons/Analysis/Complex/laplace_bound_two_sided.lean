import Mathlib
import Submission.Commons.Analysis.Calculus.exists_norm_deriv_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Calculus.derivWithin_endpoint_le
import Submission.Commons.Analysis.Calculus.dist_deriv_sub_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Complex.laplace_vertical_endpoint_tendsto

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral Filter Set
open Commons.Analysis.Calculus
open scoped Topology

/-- If `g` satisfies `‖g x‖ ≤ C` on the *open* interval `(a,b)`, then
`‖∫ x in a..b, g x‖ ≤ C * (b - a)` (for `a ≤ b`).  The bound at the endpoints is
irrelevant because a finite set is null. -/
lemma intervalIntegral_norm_le_of_bound_open {a b C : ℝ} (hab : a ≤ b) {g : ℝ → ℂ}
    (hg : ∀ x ∈ Set.Ioo a b, ‖g x‖ ≤ C) :
    ‖∫ x in a..b, g x‖ ≤ C * (b - a) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a b → ‖g x‖ ≤ C := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
      rw [ae_iff]; simp
    filter_upwards [hne] with x hx hxmem
    rw [Set.uIoc_of_le hab] at hxmem
    exact hg x ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (C := C)
    (f := g) hae
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- Pointwise bound for the Laplace kernel on `[0, x₀]`. -/
lemma norm_exp_neg_laplace_kernel_le {x₀ : ℝ} (_hx₀ : 0 ≤ x₀) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc 0 x₀) :
    ‖Complex.exp (-(z * (t:ℂ)))‖ ≤ Real.exp (x₀ * |z.re|) := by
  rw [Complex.norm_exp]
  have hre : (-(z * (t:ℂ))).re = -(z.re * t) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [hre]
  apply Real.exp_le_exp.mpr
  calc -(z.re * t) = (-z.re) * t := by ring
    _ ≤ |z.re| * t := mul_le_mul_of_nonneg_right (neg_le_abs z.re) ht.1
    _ ≤ |z.re| * x₀ := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
    _ = x₀ * |z.re| := by ring

/-- `‖1 - e^{-z x₀}‖ ≤ 2 e^{x₀ |Re z|}`. -/
lemma norm_one_sub_exp_neg_laplace_le {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (z : ℂ) :
    ‖1 - Complex.exp (-(z * (x₀:ℂ)))‖ ≤ 2 * Real.exp (x₀ * |z.re|) := by
  have h1 : ‖(1:ℂ) - Complex.exp (-(z * (x₀:ℂ)))‖
      ≤ ‖(1:ℂ)‖ + ‖Complex.exp (-(z * (x₀:ℂ)))‖ := norm_sub_le _ _
  have h2 : ‖Complex.exp (-(z * (x₀:ℂ)))‖ ≤ Real.exp (x₀ * |z.re|) :=
    norm_exp_neg_laplace_kernel_le hx₀ z ⟨hx₀, le_refl x₀⟩
  have h3 : (1:ℝ) ≤ Real.exp (x₀ * |z.re|) := Real.one_le_exp (by positivity)
  simp only [norm_one] at h1
  linarith

/-- Second-order integration by parts for the Laplace kernel, valid for **every** complex `z`
(no restriction on the real part).  This is the two-sided companion of
`Commons.Analysis.Calculus.laplace_second_IBP_alt`. -/
theorem laplace_second_IBP_general {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (z : ℂ) :
    z^2 * (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t) - z * f 0
      = derivWithin f (Set.Ioi 0) 0 * (1 - Complex.exp (-(z * (x₀:ℂ))))
        + ∫ s in (0:ℝ)..x₀,
            (Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))) * iteratedDeriv 2 f s := by
  let E : ℝ → ℂ := fun t => Complex.exp (-(z * (t : ℂ)))
  set R : ℝ := Real.exp (x₀ * |z.re|) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hfx₀ : f x₀ = 0 := hvan x₀ le_rfl
  -- basic derivative facts
  have hf' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f (deriv f t) t := fun t ht =>
    (hf2.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds ht.1 ht.2)
  have hf'' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := by
    intro t ht
    have hdiff : DifferentiableOn ℝ (deriv f) (Set.Ioo (0:ℝ) x₀) := by
      have h := hf2.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num)
        (uniqueDiffOn_Ioo 0 x₀)
      refine h.congr ?_
      intro y hy
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioo hy]
    have hd := hdiff.hasDerivAt (Ioo_mem_nhds ht.1 ht.2)
    have heq : deriv (deriv f) t = iteratedDeriv 2 f t := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [← heq]
    exact hd
  obtain ⟨D, hD⟩ := exists_norm_deriv_le_of_iteratedDeriv_two_bound hx₀ hf2 hBnd
  obtain ⟨L₀, hL₀⟩ := tendsto_nhdsGT_of_lipschitzOn_Ioo (a := (0:ℝ)) (b := x₀) hx₀ hB
    (dist_deriv_sub_le_of_iteratedDeriv_two_bound hx₀ hf2 hBnd)
  obtain ⟨L₁, hL₁⟩ := tendsto_nhdsLT_of_lipschitzOn_Ioo (a := (0:ℝ)) (b := x₀) hx₀ hB
    (dist_deriv_sub_le_of_iteratedDeriv_two_bound hx₀ hf2 hBnd)
  have hDW : derivWithin f (Set.Ioi 0) 0 = L₀ := by
    have hdiffOn : DifferentiableOn ℝ f (Set.Ioo 0 x₀) := hf2.differentiableOn (by norm_num)
    have hcont0 : ContinuousWithinAt f (Set.Ioo 0 x₀) 0 :=
      (hcont 0 ⟨le_refl 0, hx₀.le⟩).mono Ioo_subset_Icc_self
    refine (HasDerivWithinAt.mono ?_ Ioi_subset_Ici_self).derivWithin (uniqueDiffWithinAt_Ioi 0)
    exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn hcont0 (Ioo_mem_nhdsGT hx₀) hL₀
  -- E stuff
  have hE_deriv : ∀ t : ℝ, HasDerivAt E (-(z * E t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => z * (s:ℂ)) z t := by simpa using h1.const_mul z
    have h3 : HasDerivAt (fun s : ℝ => -(z * (s:ℂ))) (-z) t := h2.neg
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(z * (s:ℂ))))
        (Complex.exp (-(z*(t:ℂ))) * (-z)) t :=
      (Complex.hasDerivAt_exp (-(z*(t:ℂ)))).comp t h3
    refine h4.congr_deriv ?_
    show Complex.exp (-(z*(t:ℂ))) * (-z) = -(z * Complex.exp (-(z*(t:ℂ))))
    ring
  have hE_bound : ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖E t‖ ≤ R := by
    intro t ht
    show ‖Complex.exp (-(z * (t:ℂ)))‖ ≤ R
    rw [Complex.norm_exp, hR]
    have hre : (-(z * (t:ℂ))).re = -(z.re * t) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
    rw [hre]
    apply Real.exp_le_exp.mpr
    have ht0 : (0:ℝ) ≤ t := ht.1
    have htx : t ≤ x₀ := ht.2
    calc -(z.re * t) = (-z.re) * t := by ring
      _ ≤ |z.re| * t := mul_le_mul_of_nonneg_right (neg_le_abs z.re) ht0
      _ ≤ |z.re| * x₀ := mul_le_mul_of_nonneg_left htx (abs_nonneg _)
      _ = x₀ * |z.re| := by ring
  have hE_cont : Continuous E := by
    show Continuous (fun t : ℝ => Complex.exp (-(z * (t:ℂ))))
    exact Complex.continuous_exp.comp
      ((continuous_const : Continuous fun _ : ℝ => z).mul Complex.continuous_ofReal).neg
  have hE0 : E 0 = 1 := by
    show Complex.exp (-(z * ((0:ℝ):ℂ))) = 1
    simp
  have hf0tend : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
    have h1 : Tendsto f (𝓝[Set.Icc (0:ℝ) x₀] 0) (𝓝 (f 0)) :=
      hcont.continuousWithinAt ⟨le_refl 0, hx₀.le⟩
    have h2 : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) x₀] 0 := by
      rw [nhdsWithin_Icc_eq_nhdsGE hx₀]
      exact nhdsWithin_mono 0 Set.Ioi_subset_Ici_self
    exact h1.mono_left h2
  have hfx₀tend : Tendsto f (𝓝[<] x₀) (𝓝 (f x₀)) := by
    have h1 : Tendsto f (𝓝[Set.Icc (0:ℝ) x₀] x₀) (𝓝 (f x₀)) :=
      hcont.continuousWithinAt ⟨hx₀.le, le_refl x₀⟩
    have h2 : 𝓝[<] x₀ ≤ 𝓝[Set.Icc (0:ℝ) x₀] x₀ := by
      rw [nhdsWithin_Icc_eq_nhdsLE hx₀]
      exact nhdsWithin_mono x₀ Set.Iio_subset_Iic_self
    exact h1.mono_left h2
  have hE_tend0 : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h : Tendsto E (𝓝 (0:ℝ)) (𝓝 (E 0)) := (hE_cont.continuousAt (x := (0:ℝ))).tendsto
    rw [hE0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hE_tendx : Tendsto E (𝓝[<] x₀) (𝓝 (E x₀)) :=
    ((hE_cont.continuousAt (x := x₀)).tendsto).mono_left nhdsWithin_le_nhds
  -- first IBP
  have hK : (∫ t in (0:ℝ)..x₀, E t * deriv f t) = z * (∫ t in (0:ℝ)..x₀, E t * f t) - f 0 := by
    have hderiv1 : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
        HasDerivAt (fun s : ℝ => E s * f s) (-(z) * (E t * f t) + E t * deriv f t) t := by
      intro t ht
      exact ((hE_deriv t).mul (hf' t ht)).congr_deriv (by ring)
    have hAint : IntervalIntegrable (fun t : ℝ => -(z) * (E t * f t)) volume (0:ℝ) x₀ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx₀.le]
      exact continuous_const.continuousOn.mul (hE_cont.continuousOn.mul hcont)
    have hBint : IntervalIntegrable (fun t : ℝ => E t * deriv f t) volume (0:ℝ) x₀ := by
      refine intervalIntegrable_of_bound (C := R * D) hx₀ ?_ ?_
      · exact (hE_cont.measurable.mul (measurable_deriv f)).aestronglyMeasurable
      · intro t ht
        rw [norm_mul]
        exact mul_le_mul (hE_bound t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (hD t ht)
          (norm_nonneg _) hRpos.le
    have ha1 : Tendsto (fun s : ℝ => E s * f s) (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
      have h := hE_tend0.mul hf0tend
      simpa using h
    have hb1 : Tendsto (fun s : ℝ => E s * f s) (𝓝[<] x₀) (𝓝 0) := by
      have h := hE_tendx.mul hfx₀tend
      rw [hfx₀, mul_zero] at h
      exact h
    have hFTC1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv1
      (hAint.add hBint) ha1 hb1
    rw [intervalIntegral.integral_add hAint hBint, intervalIntegral.integral_const_mul] at hFTC1
    linear_combination hFTC1
  -- second IBP
  have hJ : (∫ s in (0:ℝ)..x₀, (E s - E x₀) * iteratedDeriv 2 f s)
      = z * (∫ t in (0:ℝ)..x₀, E t * deriv f t) - (1 - E x₀) * L₀ := by
    have hderiv3 : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
        HasDerivAt (fun s : ℝ => (E s - E x₀) * deriv f s)
          (-(z) * (E t * deriv f t) + (E t - E x₀) * iteratedDeriv 2 f t) t := by
      intro t ht
      have h1 : HasDerivAt (fun s : ℝ => E s - E x₀) (-(z * E t)) t :=
        (hE_deriv t).sub_const (E x₀)
      exact (h1.mul (hf'' t ht)).congr_deriv (by ring)
    have hAint : IntervalIntegrable (fun t : ℝ => -(z) * (E t * deriv f t)) volume (0:ℝ) x₀ := by
      refine intervalIntegrable_of_bound (C := ‖z‖ * (R * D)) hx₀ ?_ ?_
      · exact (measurable_const.mul (hE_cont.measurable.mul (measurable_deriv f))).aestronglyMeasurable
      · intro t ht
        rw [norm_mul, norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hE_bound t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (hD t ht)
            (norm_nonneg _) hRpos.le) (norm_nonneg z)
    have hBint : IntervalIntegrable (fun t : ℝ => (E t - E x₀) * iteratedDeriv 2 f t)
        volume (0:ℝ) x₀ := by
      refine intervalIntegrable_of_bound (C := (R + R) * B) hx₀ ?_ ?_
      · have h2 : iteratedDeriv 2 f = deriv (deriv f) := by
          ext t
          rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
        refine ((hE_cont.measurable.sub measurable_const).mul ?_).aestronglyMeasurable
        rw [h2]; exact measurable_deriv (deriv f)
      · intro t ht
        rw [norm_mul]
        have h1 : ‖E t - E x₀‖ ≤ R + R := by
          calc ‖E t - E x₀‖ ≤ ‖E t‖ + ‖E x₀‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add (hE_bound t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
                (hE_bound x₀ ⟨hx₀.le, le_refl x₀⟩)
        exact mul_le_mul h1 (hBnd t ht) (norm_nonneg _) (by positivity)
    have ha3 : Tendsto (fun s : ℝ => (E s - E x₀) * deriv f s) (𝓝[>] (0:ℝ))
        (𝓝 ((1 - E x₀) * L₀)) := by
      have h1 : Tendsto (fun s : ℝ => E s - E x₀) (𝓝[>] (0:ℝ)) (𝓝 (1 - E x₀)) := by
        have := hE_tend0.sub_const (E x₀)
        simpa using this
      exact h1.mul hL₀
    have hb3 : Tendsto (fun s : ℝ => (E s - E x₀) * deriv f s) (𝓝[<] x₀) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => E s - E x₀) (𝓝[<] x₀) (𝓝 0) := by
        have := hE_tendx.sub_const (E x₀)
        simpa using this
      have := h1.mul hL₁
      simpa using this
    have hFTC3 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv3
      (hAint.add hBint) ha3 hb3
    rw [intervalIntegral.integral_add hAint hBint, intervalIntegral.integral_const_mul] at hFTC3
    linear_combination hFTC3
  rw [hDW, hJ, hK]
  ring

/-- **Two-sided Laplace transform bound.**  For `f` continuous on `[0, x₀]`, `C²` on
`(0, x₀)` with `‖f''‖ ≤ B` there, vanishing for `t ≥ x₀`, and every `z ≠ 0`, one has
`‖∫₀^{x₀} e^{-zt} f(t) dt‖ ≤ ‖f 0‖ / ‖z‖ + (2‖f'(0⁺)‖ + 2B x₀) e^{x₀|Re z|} / ‖z‖²`.
This is the `L = 1`, general-`z` version of the one-sided bound, with no restriction on
the sign of `Re z` (the "two-sided" bound). -/
theorem laplace_bound_two_sided {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {z : ℂ} (hz : z ≠ 0) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t‖ ≤
      ‖f 0‖ / ‖z‖ + (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * |z.re|) / ‖z‖ ^ 2 := by
  set I : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t with hI
  set d0 : ℂ := derivWithin f (Set.Ioi 0) 0 with hd0
  set R : ℝ := Real.exp (x₀ * |z.re|) with hR
  have hRpos : 0 < R := by rw [hR]; exact Real.exp_pos _
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz2pos : 0 < ‖z‖ ^ 2 := by positivity
  set G : ℂ := ∫ s in (0:ℝ)..x₀,
      (Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))) * iteratedDeriv 2 f s with hG
  have hIBP := laplace_second_IBP_general hx₀ hB hcont hf2 hBnd hvan z
  rw [← hI, ← hd0, ← hG] at hIBP
  -- hIBP : z^2 * I - z * f 0 = d0 * (...) + G
  have hz2I : z^2 * I = z * f 0 + d0 * (1 - Complex.exp (-(z * (x₀:ℂ)))) + G := by
    have h := hIBP
    rw [sub_eq_iff_eq_add] at h
    rw [h]; ring
  -- individual bounds
  have hb1 : ‖d0 * (1 - Complex.exp (-(z * (x₀:ℂ))))‖ ≤ ‖d0‖ * (2 * R) := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg d0)
    rw [hR]; exact norm_one_sub_exp_neg_laplace_le hx₀.le z
  have hb2 : ‖G‖ ≤ 2 * R * B * x₀ := by
    rw [hG]
    have := intervalIntegral_norm_le_of_bound_open (a := (0:ℝ)) (b := x₀) (C := 2 * R * B)
      hx₀.le (g := fun s : ℝ =>
        (Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))) * iteratedDeriv 2 f s) ?_
    · simpa using this
    · intro s hs
      rw [norm_mul]
      have h1 : ‖Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))‖ ≤ R + R := by
        calc ‖Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))‖
            ≤ ‖Complex.exp (-(z * (s:ℂ)))‖ + ‖Complex.exp (-(z * (x₀:ℂ)))‖ := norm_sub_le _ _
          _ ≤ R + R := by
              rw [hR]
              exact add_le_add (norm_exp_neg_laplace_kernel_le hx₀.le z ⟨hs.1.le, hs.2.le⟩)
                (norm_exp_neg_laplace_kernel_le hx₀.le z ⟨hx₀.le, le_refl x₀⟩)
      calc ‖Complex.exp (-(z * (s:ℂ))) - Complex.exp (-(z * (x₀:ℂ)))‖ * ‖iteratedDeriv 2 f s‖
          ≤ (R + R) * B :=
            mul_le_mul h1 (hBnd s hs) (norm_nonneg _) (by positivity)
        _ = 2 * R * B := by ring
  have hkey : ‖z‖ ^ 2 * ‖I‖ ≤ ‖f 0‖ * ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R := by
    calc ‖z‖ ^ 2 * ‖I‖ = ‖z^2 * I‖ := by rw [norm_mul, norm_pow]
      _ = ‖z * f 0 + d0 * (1 - Complex.exp (-(z * (x₀:ℂ)))) + G‖ := by rw [hz2I]
      _ ≤ ‖z * f 0‖ + ‖d0 * (1 - Complex.exp (-(z * (x₀:ℂ))))‖ + ‖G‖ := norm_add₃_le
      _ ≤ ‖f 0‖ * ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R := by
          have h0 : ‖z * f 0‖ = ‖f 0‖ * ‖z‖ := by rw [norm_mul]; ring
          have h3 : ‖d0 * (1 - Complex.exp (-(z * (x₀:ℂ))))‖ ≤ (2 * ‖d0‖) * R := by
            calc ‖d0 * (1 - Complex.exp (-(z * (x₀:ℂ))))‖ ≤ ‖d0‖ * (2 * R) := hb1
              _ = (2 * ‖d0‖) * R := by ring
          have h4 : ‖G‖ ≤ (2 * B * x₀) * R := by
            calc ‖G‖ ≤ 2 * R * B * x₀ := hb2
              _ = (2 * B * x₀) * R := by ring
          linarith
  have hgoal : ‖I‖ ≤ ‖f 0‖ / ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R / ‖z‖ ^ 2 := by
    have heq : ‖f 0‖ / ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R / ‖z‖ ^ 2
        = (‖f 0‖ * ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R) / ‖z‖ ^ 2 := by
      field_simp
    rw [heq, le_div_iff₀ hz2pos]
    calc ‖I‖ * ‖z‖ ^ 2 = ‖z‖ ^ 2 * ‖I‖ := by ring
      _ ≤ ‖f 0‖ * ‖z‖ + (2 * ‖d0‖ + 2 * B * x₀) * R := hkey
  exact hgoal

end Commons.Analysis.Complex
