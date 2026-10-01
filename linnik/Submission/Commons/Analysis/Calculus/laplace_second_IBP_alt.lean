import Mathlib
import Submission.Commons.Analysis.Calculus.exists_norm_deriv_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Calculus.derivWithin_endpoint_le
import Submission.Commons.Analysis.Calculus.dist_deriv_sub_le_of_iteratedDeriv_two_bound
import Submission.Commons.Analysis.Complex.laplace_vertical_endpoint_tendsto

namespace Commons.Analysis.Calculus

open MeasureTheory intervalIntegral Filter Set
open scoped Topology

/-!
# Second-order integration by parts for the Laplace kernel, with bounded second derivative

Given `f : ℝ → ℂ` continuous on `[0, x₀]`, `C²` on `(0, x₀)` with `‖f''‖ ≤ B` there, vanishing
for `t ≥ x₀`, and `λ = w L` with `L > 0`, `Re w > 0`, two integrations by parts give

`λ² ∫₀^{x₀} e^{-λt} f(t) dt - λ f(0) = f'(0⁺)(1 - e^{-λ x₀}) + ∫₀^{x₀} (e^{-λs} - e^{-λx₀}) f''(s) ds`.

The identity is proved by applying the fundamental theorem of calculus (in the form
`integral_eq_sub_of_hasDerivAt_of_tendsto`, which only requires differentiability on the *open*
interval and one-sided limits at the endpoints) to `t ↦ e^{-λt} f(t)` and to
`t ↦ (e^{-λt} - e^{-λx₀}) f'(t)`.
-/

theorem laplace_second_IBP_alt {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    (w * (L : ℂ))^2 * (∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (L:ℂ) * (t:ℂ))) * f t)
        - w * (L : ℂ) * f 0
      = derivWithin f (Set.Ioi 0) 0 * (1 - Complex.exp (-(w * (L:ℂ) * (x₀:ℂ))))
        + ∫ s in (0:ℝ)..x₀, (Complex.exp (-(w * (L:ℂ) * (s:ℂ))) - Complex.exp (-(w * (L:ℂ) * (x₀:ℂ)))) * iteratedDeriv 2 f s := by
  set lam : ℂ := w * (L : ℂ) with hlam

  let E : ℝ → ℂ := fun t => Complex.exp (-(lam * (t : ℂ)))
  have hlam_re : 0 < lam.re := by
    rw [hlam]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos hw hL
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
  have hE_deriv : ∀ t : ℝ, HasDerivAt E (-(lam * E t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => lam * (s:ℂ)) lam t := by simpa using h1.const_mul lam
    have h3 : HasDerivAt (fun s : ℝ => -(lam * (s:ℂ))) (-lam) t := h2.neg
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(lam * (s:ℂ))))
        (Complex.exp (-(lam*(t:ℂ))) * (-lam)) t :=
      (Complex.hasDerivAt_exp (-(lam*(t:ℂ)))).comp t h3
    refine h4.congr_deriv ?_
    show Complex.exp (-(lam*(t:ℂ))) * (-lam) = -(lam * Complex.exp (-(lam*(t:ℂ))))
    ring
  have hE_bound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖E t‖ ≤ 1 := by
    intro t ht
    show ‖Complex.exp (-(lam*(t:ℂ)))‖ ≤ 1
    rw [Complex.norm_exp]
    have hre : (-(lam * (t:ℂ))).re = -(lam.re * t) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
    rw [hre, Real.exp_le_one_iff]
    nlinarith [hlam_re, ht.1]
  have hE_cont : Continuous E := by
    show Continuous (fun t : ℝ => Complex.exp (-(lam * (t:ℂ))))
    exact Complex.continuous_exp.comp (((continuous_const : Continuous fun _ : ℝ => lam)).mul
      Complex.continuous_ofReal).neg
  have hE0 : E 0 = 1 := by
    show Complex.exp (-(lam * ((0:ℝ):ℂ))) = 1
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
  have hK : (∫ t in (0:ℝ)..x₀, E t * deriv f t) = lam * (∫ t in (0:ℝ)..x₀, E t * f t) - f 0 := by
    have hderiv1 : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
        HasDerivAt (fun s : ℝ => E s * f s) (-(lam) * (E t * f t) + E t * deriv f t) t := by
      intro t ht
      exact ((hE_deriv t).mul (hf' t ht)).congr_deriv (by ring)
    have hAint : IntervalIntegrable (fun t : ℝ => -(lam) * (E t * f t)) volume (0:ℝ) x₀ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx₀.le]
      exact continuous_const.continuousOn.mul (hE_cont.continuousOn.mul hcont)
    have hBint : IntervalIntegrable (fun t : ℝ => E t * deriv f t) volume (0:ℝ) x₀ := by
      refine Commons.Analysis.Complex.intervalIntegrable_of_bound (C := D) hx₀ ?_ ?_
      · exact (hE_cont.measurable.mul (measurable_deriv f)).aestronglyMeasurable
      · intro t ht
        rw [norm_mul]
        calc ‖E t‖ * ‖deriv f t‖ ≤ 1 * D :=
              mul_le_mul (hE_bound t ht) (hD t ht) (norm_nonneg _) (by norm_num)
          _ = D := one_mul D
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
      = lam * (∫ t in (0:ℝ)..x₀, E t * deriv f t) - (1 - E x₀) * L₀ := by
    have hderiv3 : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
        HasDerivAt (fun s : ℝ => (E s - E x₀) * deriv f s)
          (-(lam) * (E t * deriv f t) + (E t - E x₀) * iteratedDeriv 2 f t) t := by
      intro t ht
      have h1 : HasDerivAt (fun s : ℝ => E s - E x₀) (-(lam * E t)) t :=
        (hE_deriv t).sub_const (E x₀)
      exact (h1.mul (hf'' t ht)).congr_deriv (by ring)
    have hAint : IntervalIntegrable (fun t : ℝ => -(lam) * (E t * deriv f t)) volume (0:ℝ) x₀ := by
      refine Commons.Analysis.Complex.intervalIntegrable_of_bound (C := ‖lam‖ * D) hx₀ ?_ ?_
      · exact (measurable_const.mul (hE_cont.measurable.mul (measurable_deriv f))).aestronglyMeasurable
      · intro t ht
        rw [norm_mul, norm_mul, norm_neg]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg lam)
        calc ‖E t‖ * ‖deriv f t‖ ≤ 1 * D :=
              mul_le_mul (hE_bound t ht) (hD t ht) (norm_nonneg _) (by norm_num)
          _ = D := one_mul D
    have hBint : IntervalIntegrable (fun t : ℝ => (E t - E x₀) * iteratedDeriv 2 f t)
        volume (0:ℝ) x₀ := by
      refine Commons.Analysis.Complex.intervalIntegrable_of_bound (C := (1 + ‖E x₀‖) * B) hx₀ ?_ ?_
      · have h2 : iteratedDeriv 2 f = deriv (deriv f) := by
          ext t
          rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
        refine ((hE_cont.measurable.sub measurable_const).mul ?_).aestronglyMeasurable
        rw [h2]; exact measurable_deriv (deriv f)
      · intro t ht
        rw [norm_mul]
        have h1 : ‖E t - E x₀‖ ≤ 1 + ‖E x₀‖ := by
          calc ‖E t - E x₀‖ ≤ ‖E t‖ + ‖E x₀‖ := norm_sub_le _ _
            _ ≤ 1 + ‖E x₀‖ := by linarith [hE_bound t ht]
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

end Commons.Analysis.Calculus
