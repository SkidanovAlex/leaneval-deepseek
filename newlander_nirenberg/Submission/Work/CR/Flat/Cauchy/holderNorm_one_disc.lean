import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.dbarC_cauchyTransform
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_le
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_le
import Submission.Work.CR.Flat.Cauchy.fderiv_eq_dzC_add_dbarC
import Submission.Work.CR.Flat.Cauchy.integral_dzC_div_eq_integral_sub_div_sq
import Submission.Work.CR.Flat.Cauchy.dzC_integral_translate
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_sub_le_explicit

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-! ## Schauder estimate for the Cauchy potential on a disc

`holderNorm_one_disc` is the "gain of exactly one derivative" estimate for the Cauchy potential
`T f = cauchyTransform ρ f` on the disc of radius `ρ/2`, in the `C^{k,α}` norm of
`Submission/Work/CR/Flat/Holder.lean`.

The proof is the standard assembly:

* `∂̄ (T f) = f` (`dbarC_cauchyTransform`) and `∂_z (T f) = S f` (`dzC_cauchyTransform`), so the
  real differential of `T f` is controlled pointwise by `‖S f‖ + ‖f‖` and its differences by
  `‖S f x - S f y‖ + ‖f x - f y‖` (`norm_fderiv_le_norm_dzC_add_dbarC`,
  `norm_fderiv_sub_le_norm_dzC_sub_add`);
* the pointwise and Hölder bounds for `T f` (`norm_cauchyTransform_le`,
  `norm_cauchyTransform_sub_le`);
* the Calderón–Zygmund bound for the Beurling transform (`norm_beurlingTransform_le`, and the
  linear-in-the-Hölder-constant form `norm_beurlingTransform_sub_le_explicit`).

The auxiliary calculus lemmas used here are proved in this file so that the result does not depend
on the (parallel) development of the `C^{1,α}` Schauder estimate for `cauchyTransform`. -/

/-- `∂_z` of a constant multiple.  No differentiability hypothesis is needed: `fderiv` is `0`
where the function is not differentiable, and multiplication by a nonzero constant preserves
(non-)differentiability. -/
lemma dzC_const_mul (c : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    dzC (fun z => c * g z) z = c * dzC g z := by
  by_cases hc : c = 0
  · subst hc
    simp [dzC]
  · by_cases hg : DifferentiableAt ℝ g z
    · unfold dzC
      rw [fderiv_const_mul hg c]
      simp only [smul_apply, smul_eq_mul]
      ring
    · have h2 : ¬ DifferentiableAt ℝ (fun z => c * g z) z := by
        intro h
        refine hg ?_
        have h3 : DifferentiableAt ℝ (fun z => c⁻¹ * (c * g z)) z := h.const_mul c⁻¹
        convert h3 using 1
        ext w
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      simp only [dzC, fderiv_zero_of_not_differentiableAt h2,
        fderiv_zero_of_not_differentiableAt hg, zero_apply, mul_zero, sub_zero]

/-- `∂_z` of a translate: `∂_z (x ↦ f (z + x)) w = (∂_z f) (z + w)`. -/
lemma dzC_comp_add (f : ℂ → ℂ) (z w : ℂ) :
    dzC (fun x => f (z + x)) w = dzC f (z + w) := by
  by_cases hf : DifferentiableAt ℝ f (z + w)
  · have hτ : DifferentiableAt ℝ (fun x : ℂ => z + x) w := by fun_prop
    have hderiv : fderiv ℝ (fun x : ℂ => z + x) w = ContinuousLinearMap.id ℝ ℂ := by
      have h1 : (fun x : ℂ => z + x) = fun x : ℂ => x + z := by funext x; rw [add_comm]
      rw [h1, fderiv_add_const]
      simp
    have hfd : fderiv ℝ (fun x => f (z + x)) w = fderiv ℝ f (z + w) := by
      rw [show (fun x => f (z + x)) = f ∘ (fun x : ℂ => z + x) from rfl,
        fderiv_comp w hf hτ, hderiv]
      rfl
    simp only [dzC, hfd]
  · have h2 : ¬ DifferentiableAt ℝ (fun x => f (z + x)) w := by
      intro h
      have h' : DifferentiableAt ℝ (fun x : ℂ => f (z + x)) ((z + w) - z) := by
        rw [show (z + w) - z = w from by ring]; exact h
      have hτ : DifferentiableAt ℝ (fun y : ℂ => y - z) (z + w) := by fun_prop
      have h1 : DifferentiableAt ℝ ((fun x : ℂ => f (z + x)) ∘ (fun y : ℂ => y - z)) (z + w) :=
        h'.comp (z + w) hτ
      have heq : ((fun x : ℂ => f (z + x)) ∘ (fun y : ℂ => y - z)) = f := by
        funext y
        simp only [Function.comp_apply]
        rw [show z + (y - z) = y from by ring]
      rw [heq] at h1
      exact hf h1
    simp only [dzC, fderiv_zero_of_not_differentiableAt h2,
      fderiv_zero_of_not_differentiableAt hf, zero_apply]

/-- `∂̄` of a translate: `∂̄ (x ↦ f (z + x)) w = (∂̄ f) (z + w)`. -/
lemma dbarC_comp_add (f : ℂ → ℂ) (z w : ℂ) :
    dbarC (fun x => f (z + x)) w = dbarC f (z + w) := by
  by_cases hf : DifferentiableAt ℝ f (z + w)
  · have hτ : DifferentiableAt ℝ (fun x : ℂ => z + x) w := by fun_prop
    have hderiv : fderiv ℝ (fun x : ℂ => z + x) w = ContinuousLinearMap.id ℝ ℂ := by
      have h1 : (fun x : ℂ => z + x) = fun x : ℂ => x + z := by funext x; rw [add_comm]
      rw [h1, fderiv_add_const]
      simp
    have hfd : fderiv ℝ (fun x => f (z + x)) w = fderiv ℝ f (z + w) := by
      rw [show (fun x => f (z + x)) = f ∘ (fun x : ℂ => z + x) from rfl,
        fderiv_comp w hf hτ, hderiv]
      rfl
    simp only [dbarC, hfd]
  · have h2 : ¬ DifferentiableAt ℝ (fun x => f (z + x)) w := by
      intro h
      have h' : DifferentiableAt ℝ (fun x : ℂ => f (z + x)) ((z + w) - z) := by
        rw [show (z + w) - z = w from by ring]; exact h
      have hτ : DifferentiableAt ℝ (fun y : ℂ => y - z) (z + w) := by fun_prop
      have h1 : DifferentiableAt ℝ ((fun x : ℂ => f (z + x)) ∘ (fun y : ℂ => y - z)) (z + w) :=
        h'.comp (z + w) hτ
      have heq : ((fun x : ℂ => f (z + x)) ∘ (fun y : ℂ => y - z)) = f := by
        funext y
        simp only [Function.comp_apply]
        rw [show z + (y - z) = y from by ring]
      rw [heq] at h1
      exact hf h1
    simp only [dbarC, fderiv_zero_of_not_differentiableAt h2,
      fderiv_zero_of_not_differentiableAt hf, zero_apply]

/-- The real differential is controlled by the two Wirtinger derivatives:
`‖(du)_z‖ ≤ ‖∂u(z)‖ + ‖∂̄u(z)‖`. -/
lemma norm_fderiv_le_norm_dzC_add_dbarC (u : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ u z‖ ≤ ‖dzC u z‖ + ‖dbarC u z‖ := by
  by_cases hu : DifferentiableAt ℝ u z
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [fderiv_eq_dzC_add_dbarC u z v hu]
    calc ‖dzC u z * v + dbarC u z * star v‖
        ≤ ‖dzC u z * v‖ + ‖dbarC u z * star v‖ := norm_add_le _ _
      _ = ‖dzC u z‖ * ‖v‖ + ‖dbarC u z‖ * ‖v‖ := by
          rw [norm_mul, norm_mul, norm_star]
      _ = (‖dzC u z‖ + ‖dbarC u z‖) * ‖v‖ := by ring
  · rw [fderiv_zero_of_not_differentiableAt hu]
    simp only [norm_zero]
    positivity

/-- The difference of two real differentials is controlled by the differences of the two
Wirtinger derivatives. -/
lemma norm_fderiv_sub_le_norm_dzC_sub_add (u : ℂ → ℂ) (x y : ℂ) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖
      ≤ ‖dzC u x - dzC u y‖ + ‖dbarC u x - dbarC u y‖ := by
  by_cases hx : DifferentiableAt ℝ u x
  · by_cases hy : DifferentiableAt ℝ u y
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have h1 := fderiv_eq_dzC_add_dbarC u x v hx
      have h2 := fderiv_eq_dzC_add_dbarC u y v hy
      have h3 : (fderiv ℝ u x - fderiv ℝ u y) v
          = (dzC u x - dzC u y) * v + (dbarC u x - dbarC u y) * star v := by
        simp only [sub_apply]
        rw [h1, h2]; ring
      rw [h3]
      calc ‖(dzC u x - dzC u y) * v + (dbarC u x - dbarC u y) * star v‖
          ≤ ‖dzC u x - dzC u y‖ * ‖v‖ + ‖dbarC u x - dbarC u y‖ * ‖v‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_star]
        _ = (‖dzC u x - dzC u y‖ + ‖dbarC u x - dbarC u y‖) * ‖v‖ := by ring
    · have hyd : fderiv ℝ u y = 0 := fderiv_zero_of_not_differentiableAt hy
      have hzd : dzC u y = 0 := by simp only [dzC, hyd, zero_apply, sub_self, mul_zero]
      have hbd : dbarC u y = 0 := by simp only [dbarC, hyd, zero_apply, add_zero, mul_zero]
      rw [hyd, hzd, hbd]
      simpa using norm_fderiv_le_norm_dzC_add_dbarC u x
  · have hxd : fderiv ℝ u x = 0 := fderiv_zero_of_not_differentiableAt hx
    have hzd : dzC u x = 0 := by simp only [dzC, hxd, zero_apply, sub_self, mul_zero]
    have hbd : dbarC u x = 0 := by simp only [dbarC, hxd, zero_apply, add_zero, mul_zero]
    rw [hxd, hzd, hbd]
    by_cases hy : DifferentiableAt ℝ u y
    · simpa using norm_fderiv_le_norm_dzC_add_dbarC u y
    · have hyd : fderiv ℝ u y = 0 := fderiv_zero_of_not_differentiableAt hy
      have hzd' : dzC u y = 0 := by simp only [dzC, hyd, zero_apply, sub_self, mul_zero]
      have hbd' : dbarC u y = 0 := by simp only [dbarC, hyd, zero_apply, add_zero, mul_zero]
      rw [hyd, hzd', hbd']
      simp

/-- A `C¹` function vanishing off the closed ball of radius `ρ` has bounded differential: the
differential is continuous and vanishes off the compact closed ball. -/
lemma exists_norm_fderiv_le_of_support {ρ : ℝ} {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall ρ f) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ z : ℂ, ‖fderiv ℝ f z‖ ≤ Λ := by
  have hcont : Continuous fun z : ℂ => ‖fderiv ℝ f z‖ :=
    (hf.continuous_fderiv (by norm_num)).norm
  have hzero : ∀ z : ℂ, ρ < ‖z‖ → fderiv ℝ f z = 0 := by
    intro z hz
    have hε : 0 < ‖z‖ - ρ := by linarith
    have hev : f =ᶠ[nhds z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      refine hfsupp w ?_
      have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
        have := norm_add_le w (z - w)
        simpa using this
      have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
      linarith [hw]
    rw [hev.fderiv_eq]
    simp
  obtain ⟨Λ₀, hΛ₀⟩ :=
    (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image hcont.continuousOn
  refine ⟨max Λ₀ 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ ρ
  · have hzmem : z ∈ Metric.closedBall (0 : ℂ) ρ := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact (hΛ₀ (Set.mem_image_of_mem _ hzmem)).trans (le_max_left _ _)
  · rw [hzero z (not_le.mp hz), norm_zero]
    exact le_max_right _ _

/-- The real differential dominated by the Wirtinger derivatives gives the pointwise bound
`‖∂_z u‖ ≤ ‖du‖`; used to dominate `∂_z F / w` by `Λ/‖w‖`. -/
lemma norm_dzC_le_norm_fderiv (u : ℂ → ℂ) (z : ℂ) : ‖dzC u z‖ ≤ ‖fderiv ℝ u z‖ := by
  rw [dzC]
  calc ‖(1/2 : ℂ) * (fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I)‖
      = (1/2) * ‖fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I‖ := by
        rw [norm_mul]; norm_num
    _ ≤ (1/2) * (‖fderiv ℝ u z 1‖ + ‖Complex.I * fderiv ℝ u z Complex.I‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1/2) * (‖fderiv ℝ u z‖ + ‖fderiv ℝ u z‖) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · simpa using (fderiv ℝ u z).le_opNorm 1
        · simpa [Complex.norm_I] using (fderiv ℝ u z).le_opNorm Complex.I
    _ = ‖fderiv ℝ u z‖ := by ring

/-- The Cauchy potential has `∂_z`-derivative equal to the Beurling transform. -/
theorem dzC_cauchyTransform {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall (ρ / 2) f) {z : ℂ} (hz : ‖z‖ < ρ / 2) :
    dzC (cauchyTransform ρ f) z = beurlingTransform ρ f z := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_norm_fderiv_le_of_support (ρ := ρ) hf
    (fun w hw => hfsupp w (by linarith))
  set F : ℂ → ℂ := fun w => f (z + w) with hF
  have hFsupp : SupportedInBall ρ F := by
    intro w hw
    simp only [hF]
    refine hfsupp (z + w) ?_
    have h1 : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
      have h := norm_sub_le (w + z) z
      rwa [add_sub_cancel_right] at h
    have h2 : ‖z + w‖ = ‖w + z‖ := by rw [add_comm]
    linarith
  have hF1 : ContDiff ℝ 1 F := by
    rw [hF]
    exact hf.comp (contDiff_const.add contDiff_id)
  have hdzCF : ∀ w : ℂ, ‖dzC F w‖ ≤ Λ := by
    intro w
    have h1 : dzC F w = dzC f (z + w) := by rw [hF]; exact dzC_comp_add f z w
    rw [h1]
    exact (norm_dzC_le_norm_fderiv f (z + w)).trans (hΛ (z + w))
  -- integrability of `∂_z F w / w`
  have hint1 : IntegrableOn (fun w : ℂ => dzC F w / w) (Metric.ball (0 : ℂ) ρ) := by
    have hmaj : IntegrableOn (fun w : ℂ => Λ * ‖w‖⁻¹) (Metric.ball (0 : ℂ) ρ) := by
      have h1 : IntegrableOn (fun w : ℂ => ‖w⁻¹‖) (Metric.ball (0 : ℂ) ρ) :=
        (integrableOn_inv_ball ρ).norm
      refine (h1.const_mul Λ).congr ?_
      filter_upwards with w
      rw [norm_inv]
    have hfderiv : Continuous fun w : ℂ => fderiv ℝ F w := hF1.continuous_fderiv (by norm_num)
    have hmeasM : Measurable fun w : ℂ => dzC F w / w := by
      have hcont : Continuous fun w : ℂ => dzC F w := by
        rw [show (fun w : ℂ => dzC F w)
            = fun w : ℂ => (1/2 : ℂ) * ((fderiv ℝ F w) 1 - Complex.I * (fderiv ℝ F w) Complex.I)
          from by funext w; rfl]
        exact (((hfderiv.clm_apply continuous_const).sub
          (continuous_const.mul (hfderiv.clm_apply continuous_const))).const_mul _)
      have hdiv : (fun w : ℂ => dzC F w / w) = fun w : ℂ => dzC F w * w⁻¹ := by
        funext w; rw [div_eq_mul_inv]
      rw [hdiv]
      exact hcont.measurable.mul measurable_inv
    refine hmaj.mono' hmeasM.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_div]
    calc ‖dzC F w‖ / ‖w‖ ≤ Λ / ‖w‖ := div_le_div_of_nonneg_right (hdzCF w) (norm_nonneg w)
      _ = Λ * ‖w‖⁻¹ := by rw [div_eq_mul_inv]
  have hint2 : IntegrableOn (fun w : ℂ => dzC F 0 / w) (Metric.ball (0 : ℂ) ρ) := by
    have hconst : (fun w : ℂ => dzC F 0 / w) = fun w : ℂ => dzC F 0 * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [hconst]
    exact (integrableOn_inv_ball ρ).const_mul _
  -- Step 1: pull out the normalisation constant and differentiate under the integral sign.
  have h1 : dzC (cauchyTransform ρ f) z
      = -((Real.pi : ℂ))⁻¹ *
          dzC (fun z : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w) z :=
    dzC_const_mul _ _ _
  rw [h1, dzC_integral_translate hf z]
  -- Step 2: rewrite the integrand as a difference of `∂_z F` at `w` and at `0`.
  have h2 : ∫ w in Metric.ball (0 : ℂ) ρ, (dzC f (z + w) - dzC f z) / w
      = ∫ w in Metric.ball (0 : ℂ) ρ, (dzC F w - dzC F 0) / w := by
    refine setIntegral_congr_fun measurableSet_ball fun w _ => ?_
    have hw1 : dzC F w = dzC f (z + w) := by rw [hF]; exact dzC_comp_add f z w
    have hw2 : dzC F 0 = dzC f (z + 0) := by rw [hF]; exact dzC_comp_add f z 0
    rw [hw1, hw2, add_zero]
  rw [h2]
  -- Step 3: the mean-zero of `1/w` kills the constant term.
  have h3 : ∫ w in Metric.ball (0 : ℂ) ρ, (dzC F w - dzC F 0) / w
      = ∫ w in Metric.ball (0 : ℂ) ρ, dzC F w / w := by
    have hsplit : (fun w : ℂ => (dzC F w - dzC F 0) / w)
        = fun w : ℂ => dzC F w / w - dzC F 0 / w := by
      funext w; rw [sub_div]
    rw [hsplit, integral_sub hint1 hint2]
    have hzero : ∫ w in Metric.ball (0 : ℂ) ρ, dzC F 0 / w = 0 := by
      have hconst : (fun w : ℂ => dzC F 0 / w) = fun w : ℂ => dzC F 0 * w⁻¹ := by
        funext w; rw [div_eq_mul_inv]
      rw [hconst, integral_const_mul, integral_inv_ball, mul_zero]
    rw [hzero, sub_zero]
  rw [h3]
  -- Step 4: the kernel identity.
  have h4 : ∫ w in Metric.ball (0 : ℂ) ρ, dzC F w / w
      = ∫ w in Metric.ball (0 : ℂ) ρ, (F w - F 0) / w ^ 2 :=
    integral_dzC_div_eq_integral_sub_div_sq hρ hF1 hFsupp
  rw [h4]
  -- Step 5: identify the resulting integral with the Beurling transform.
  have h5 : (fun w : ℂ => (F w - F 0) / w ^ 2) = fun w : ℂ => (f (z + w) - f z) / w ^ 2 := by
    funext w; rw [hF]; simp
  rw [h5]
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h6 : -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w ^ 2
      = beurlingTransform ρ f z := by
    rw [beurlingTransform]
  exact h6

/-- For `i = 0` the iterated derivative at `x` is the constant multilinear map `m ↦ f x`, so the
norm of the difference of the two iterated derivatives is the norm of the difference of the
values. -/
lemma norm_iteratedFDerivWithin_zero_sub (f : ℂ → ℂ) (Ω : Set ℂ) (x y : ℂ) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y) (0 : Fin 0 → ℂ)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → ℂ) i‖) = 1 from by simp, mul_one] at h
    exact h

/-- Unfolding `holderNorm` at `k = 0`. -/
lemma holderNorm_zero_eq (α : ℝ) (f : ℂ → ℂ) (Ω : Set ℂ) :
    holderNorm 0 α f Ω = iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- Unfolding `holderNorm` at `k = 1`. -/
lemma holderNorm_one_eq (α : ℝ) (f : ℂ → ℂ) (Ω : Set ℂ) :
    holderNorm 1 α f Ω
      = (iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω)
        + (iterDerivNorm 1 f Ω + holderSeminorm 1 α f Ω) := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- **Schauder estimate for the Cauchy potential on a disc** ("a gain of exactly one
derivative"): there is a constant `C = C(ρ,α)` such that for every `C¹` function `f` supported in
the disc of radius `ρ/2`, the Cauchy potential `T f = cauchyTransform ρ f` satisfies

`‖T f‖_{C^{1,α}(ball 0 (ρ/2))} ≤ C · ‖f‖_{C^{0,α}(ℂ)}`.

The `C^{1,α}` norm is the one of `Submission/Work/CR/Flat/Holder.lean`, and
`‖f‖_{C^{0,α}(ℂ)}` is `holderNorm 0 α f univ`.  The ingredients are `∂̄(T f) = f`
(`dbarC_cauchyTransform`), `∂_z(T f) = S f` (`dzC_cauchyTransform`), the pointwise and Hölder
estimates for `T f` (`norm_cauchyTransform_le`, `norm_cauchyTransform_sub_le`) and the boundedness
of the Beurling transform `S` on `C^{0,α}` (`norm_beurlingTransform_le`,
`norm_beurlingTransform_sub_le_explicit`, the classical Calderón–Zygmund estimate with kernel
`(ζ-z)^{-2}`).  The constant `C` is uniform in `f`. -/
theorem holderNorm_one_disc {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → SupportedInBall (ρ / 2) f →
      holderNorm 1 α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
        ≤ ENNReal.ofReal C * holderNorm 0 α f Set.univ := by
  obtain ⟨CB, hCBpos, hCB⟩ :=
    norm_beurlingTransform_sub_le_explicit (ρ := ρ) (α := α) hρ hα hα1
  set cK : ℝ := 2 * ρ ^ (α + 1) / (α + 1) + 8 * ρ + 2 * ρ ^ α / α + (1 + CB) with hcK
  have hcK0 : 0 ≤ cK := by
    rw [hcK]
    have h1 : 0 < ρ ^ (α + 1) := Real.rpow_pos_of_pos hρ (α + 1)
    have h2 : 0 < α + 1 := by linarith
    have h3 : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
    have h4 : 0 < 1 + CB := by linarith
    positivity
  refine ⟨cK + 1, by linarith, ?_⟩
  intro f hf hfsupp
  set Ω : Set ℂ := Metric.ball 0 (ρ / 2) with hΩdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Metric.isOpen_ball
  have hCpos : (0 : ℝ) < cK + 1 := by linarith
  by_cases hS : iterDerivNorm 0 f Set.univ = ⊤
  · have h0 : holderNorm 0 α f Set.univ = ⊤ := by
      rw [holderNorm_zero_eq, hS]
      simp
    rw [h0, ENNReal.mul_top (by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hCpos)]
    exact le_top
  by_cases hH : holderSeminorm 0 α f Set.univ = ⊤
  · have h0 : holderNorm 0 α f Set.univ = ⊤ := by
      rw [holderNorm_zero_eq, hH]
      simp
    rw [h0, ENNReal.mul_top (by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hCpos)]
    exact le_top
  · -- the finite case: extract the sup norm `A` and the Hölder constant `K`
    set A : ℝ := (iterDerivNorm 0 f Set.univ).toReal with hAdef
    set K : ℝ := (holderSeminorm 0 α f Set.univ).toReal with hKdef
    have hA0 : 0 ≤ A := hAdef ▸ ENNReal.toReal_nonneg
    have hK0 : 0 ≤ K := hKdef ▸ ENNReal.toReal_nonneg
    have hS' : ENNReal.ofReal A = iterDerivNorm 0 f Set.univ :=
      hAdef ▸ ENNReal.ofReal_toReal hS
    have hH' : ENNReal.ofReal K = holderSeminorm 0 α f Set.univ :=
      hKdef ▸ ENNReal.ofReal_toReal hH
    have hfA : ∀ x : ℂ, ‖f x‖ ≤ A := by
      intro x
      have h1 : ENNReal.ofReal ‖f x‖ ≤ iterDerivNorm 0 f Set.univ := by
        rw [iterDerivNorm_zero]
        exact le_iSup₂_of_le x (Set.mem_univ x) le_rfl
      rw [← hS'] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hA0).mp h1
    have hfK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α := by
      intro x y
      rcases eq_or_ne x y with rfl | hxy
      · simp [Real.zero_rpow (ne_of_gt hα)]
      · have h1 : ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
            ≤ holderSeminorm 0 α f Set.univ := by
          have h := le_holderSeminorm 0 α f Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
          rwa [norm_iteratedFDerivWithin_zero_sub f Set.univ x y] at h
        rw [← hH'] at h1
        have h2 : ‖f x - f y‖ / ‖x - y‖ ^ α ≤ K := (ENNReal.ofReal_le_ofReal_iff hK0).mp h1
        have h3 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        rwa [div_le_iff₀ h3] at h2
    -- the four terms of the `C^{1,α}` norm
    have hT0 : iterDerivNorm 0 (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal (2 * K * ρ ^ (α + 1) / (α + 1)) := by
      rw [iterDerivNorm_zero]
      refine iSup₂_le fun x hx => ?_
      have hxρ : ‖x‖ < ρ := by
        rw [hΩdef, Metric.mem_ball, dist_zero_right] at hx
        linarith
      exact ENNReal.ofReal_le_ofReal (norm_cauchyTransform_le hα hK0 hfK hxρ)
    have hT1 : holderSeminorm 0 α (cauchyTransform ρ f) Ω ≤ ENNReal.ofReal (8 * K * ρ) := by
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      have hxmem : x ∈ Metric.ball (0 : ℂ) (ρ / 2) := by rw [← hΩdef]; exact hx
      have hymem : y ∈ Metric.ball (0 : ℂ) (ρ / 2) := by rw [← hΩdef]; exact hy
      rw [norm_iteratedFDerivWithin_zero_sub (cauchyTransform ρ f) Ω x y]
      have hb : ‖cauchyTransform ρ f x - cauchyTransform ρ f y‖ ≤ 8 * K * ρ * ‖x - y‖ ^ α :=
        norm_cauchyTransform_sub_le hα hK0 hfK hxmem hymem
      have h3 : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ h3]
      linarith [hb]
    have hT2 : iterDerivNorm 1 (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal (2 * K * ρ ^ α / α + A) := by
      refine iSup₂_le fun x hx => ?_
      have hxmem : x ∈ Metric.ball (0 : ℂ) (ρ / 2) := by rw [← hΩdef]; exact hx
      have hxlt : ‖x‖ < ρ / 2 := by
        rw [Metric.mem_ball, dist_zero_right] at hxmem; exact hxmem
      have hxρ : ‖x‖ < ρ := by linarith
      have hnorm : ‖iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω x‖
          = ‖fderiv ℝ (cauchyTransform ρ f) x‖ := by
        rw [norm_iteratedFDerivWithin_one _ (hΩopen.uniqueDiffWithinAt hx),
          fderivWithin_of_isOpen hΩopen hx]
      rw [hnorm]
      have hbd := norm_fderiv_le_norm_dzC_add_dbarC (cauchyTransform ρ f) x
      rw [dzC_cauchyTransform hρ hf hfsupp hxlt,
        dbarC_cauchyTransform hρ hf hfsupp hxlt] at hbd
      have hb1 : ‖beurlingTransform ρ f x‖ ≤ 2 * K * ρ ^ α / α :=
        norm_beurlingTransform_le hα hK0 hfK hxρ
      have hb2 : ‖f x‖ ≤ A := hfA x
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    have hT3 : holderSeminorm 1 α (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal ((1 + CB) * K) := by
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      have hxmem : x ∈ Metric.ball (0 : ℂ) (ρ / 2) := by rw [← hΩdef]; exact hx
      have hymem : y ∈ Metric.ball (0 : ℂ) (ρ / 2) := by rw [← hΩdef]; exact hy
      have hxlt : ‖x‖ < ρ / 2 := by
        rw [Metric.mem_ball, dist_zero_right] at hxmem; exact hxmem
      have hylt : ‖y‖ < ρ / 2 := by
        rw [Metric.mem_ball, dist_zero_right] at hymem; exact hymem
      have hnorm : ‖iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω x
            - iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω y‖
          ≤ ‖fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y‖ := by
        refine ContinuousMultilinearMap.opNorm_le_bound
          (M := ‖fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y‖)
          (norm_nonneg _) fun m => ?_
        have key : (iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω x
              - iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω y) m
            = (fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y) (m 0) := by
          rw [ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.sub_apply,
            iteratedFDerivWithin_one_apply (hΩopen.uniqueDiffWithinAt hx),
            iteratedFDerivWithin_one_apply (hΩopen.uniqueDiffWithinAt hy),
            fderivWithin_of_isOpen hΩopen hx, fderivWithin_of_isOpen hΩopen hy]
        rw [key]
        have hprod : (∏ i : Fin 1, ‖m i‖) = ‖m 0‖ := by simp
        calc ‖(fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y) (m 0)‖
            ≤ ‖fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y‖ * ‖m 0‖ :=
              (fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y).le_opNorm
                (m 0)
          _ = ‖fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y‖
                * ∏ i : Fin 1, ‖m i‖ := by rw [hprod]
      have hbd := norm_fderiv_sub_le_norm_dzC_sub_add (cauchyTransform ρ f) x y
      have hdz : dzC (cauchyTransform ρ f) x - dzC (cauchyTransform ρ f) y
          = beurlingTransform ρ f x - beurlingTransform ρ f y := by
        rw [dzC_cauchyTransform hρ hf hfsupp hxlt, dzC_cauchyTransform hρ hf hfsupp hylt]
      have hdb : dbarC (cauchyTransform ρ f) x - dbarC (cauchyTransform ρ f) y
          = f x - f y := by
        rw [dbarC_cauchyTransform hρ hf hfsupp hxlt, dbarC_cauchyTransform hρ hf hfsupp hylt]
      rw [hdz, hdb] at hbd
      have hb1 : ‖beurlingTransform ρ f x - beurlingTransform ρ f y‖ ≤ CB * K * ‖x - y‖ ^ α :=
        hCB hK0 hfK hfsupp x hxmem y hymem
      have hb2 : ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α := hfK x y
      have h3 : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have h5 : ‖iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω x
            - iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω y‖
          ≤ (CB * K + K) * ‖x - y‖ ^ α := by
        calc ‖iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω x
              - iteratedFDerivWithin ℝ 1 (cauchyTransform ρ f) Ω y‖
            ≤ ‖fderiv ℝ (cauchyTransform ρ f) x - fderiv ℝ (cauchyTransform ρ f) y‖ := hnorm
          _ ≤ ‖beurlingTransform ρ f x - beurlingTransform ρ f y‖ + ‖f x - f y‖ := hbd
          _ ≤ CB * K * ‖x - y‖ ^ α + K * ‖x - y‖ ^ α := add_le_add hb1 hb2
          _ = (CB * K + K) * ‖x - y‖ ^ α := by ring
      have h6 : CB * K + K ≤ (1 + CB) * K := by linarith [hK0, hCBpos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ h3]
      exact h5.trans (mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg (norm_nonneg _) α))
    -- combine the four bounds
    have h12 : iterDerivNorm 0 (cauchyTransform ρ f) Ω
          + holderSeminorm 0 α (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal (2 * K * ρ ^ (α + 1) / (α + 1)) + ENNReal.ofReal (8 * K * ρ) :=
      add_le_add hT0 hT1
    have h34 : iterDerivNorm 1 (cauchyTransform ρ f) Ω
          + holderSeminorm 1 α (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal (2 * K * ρ ^ α / α + A) + ENNReal.ofReal ((1 + CB) * K) :=
      add_le_add hT2 hT3
    have hmain : holderNorm 1 α (cauchyTransform ρ f) Ω ≤ ENNReal.ofReal (cK * K + A) := by
      rw [holderNorm_one_eq]
      refine (add_le_add h12 h34).trans ?_
      have e1 : ENNReal.ofReal (2 * K * ρ ^ (α + 1) / (α + 1)) + ENNReal.ofReal (8 * K * ρ)
          = ENNReal.ofReal (2 * K * ρ ^ (α + 1) / (α + 1) + 8 * K * ρ) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      have e2 : ENNReal.ofReal (2 * K * ρ ^ α / α + A) + ENNReal.ofReal ((1 + CB) * K)
          = ENNReal.ofReal ((2 * K * ρ ^ α / α + A) + (1 + CB) * K) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      have e3 : ENNReal.ofReal (2 * K * ρ ^ (α + 1) / (α + 1) + 8 * K * ρ)
            + ENNReal.ofReal ((2 * K * ρ ^ α / α + A) + (1 + CB) * K)
          = ENNReal.ofReal ((2 * K * ρ ^ (α + 1) / (α + 1) + 8 * K * ρ)
              + ((2 * K * ρ ^ α / α + A) + (1 + CB) * K)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      rw [e1, e2, e3]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hcK]
      have harith : (2 * K * ρ ^ (α + 1) / (α + 1) + 8 * K * ρ)
            + ((2 * K * ρ ^ α / α + A) + (1 + CB) * K)
          = (2 * ρ ^ (α + 1) / (α + 1) + 8 * ρ + 2 * ρ ^ α / α + (1 + CB)) * K + A := by ring
      rw [harith]
    have hAK : cK * K + A ≤ (cK + 1) * (A + K) := by
      nlinarith [hA0, hK0, hcK0]
    have h0 : holderNorm 0 α f Set.univ = ENNReal.ofReal A + ENNReal.ofReal K := by
      rw [holderNorm_zero_eq, hS', hH']
    calc holderNorm 1 α (cauchyTransform ρ f) Ω
        ≤ ENNReal.ofReal (cK * K + A) := hmain
      _ ≤ ENNReal.ofReal ((cK + 1) * (A + K)) := ENNReal.ofReal_le_ofReal hAK
      _ = ENNReal.ofReal (cK + 1) * ENNReal.ofReal (A + K) :=
            ENNReal.ofReal_mul (by linarith)
      _ = ENNReal.ofReal (cK + 1) * (ENNReal.ofReal A + ENNReal.ofReal K) := by
            rw [ENNReal.ofReal_add hA0 hK0]
      _ = ENNReal.ofReal (cK + 1) * holderNorm 0 α f Set.univ := by rw [h0]

end Work.CR.Flat.Cauchy
