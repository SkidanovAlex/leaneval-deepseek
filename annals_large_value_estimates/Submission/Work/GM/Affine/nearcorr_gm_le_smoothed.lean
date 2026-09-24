import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.rho_kernel_domination
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup

/-!
# GM §9: the individual pieces `g_m` are dominated by the smoothed profile

For `m ∈ R2 M₂` (i.e. `M₂ < m ≤ 2M₂`) the `m`-th piece of the smoothed profile,
`gm f s m u = ∫ f u' · (m/s) ψ (m (u-u')/s)` with `s = smScale K T M₂ = M₂/(2KT)`,
is bounded by `4K` times the smoothed profile `f̃ = smoothed ψSmooth T f`.

The dilate `(m/s) = 2KTm/M₂` of the kernel is at least `16 T` times as large as the
scale `T` of the smoothed profile, so the two kernels can be compared *pointwise at the
same argument* (`rho_kernel_domination`), and the integral inequality follows by
monotonicity of the integral against the nonnegative function `f`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem nearcorr_gm_le_smoothed {K T M₂ : ℝ} (hT : 1 ≤ T) (hK : 8 ≤ K) (hM₂ : 1 ≤ M₂)
    {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (hf : MeasureTheory.Integrable f) {m : ℤ} (hm : m ∈ R2 M₂) (u : ℝ) :
    gm f (smScale K T M₂) m u ≤ 4 * K * smoothed psiSmooth T f u := by
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hspos : 0 < smScale K T M₂ := smScale_pos hKpos hTpos hM₂pos
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hmem
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : 0 < (m : ℝ) := by linarith
  have hψle : ∀ x : ℝ, psiSmooth x ≤ 1 / ∫ y, psiBump y := fun x => rho_psiSmooth_le_inv_integral x
  -- The kernel `(m/s) ψ (m · /s)` is dominated, at the same argument, by `4KT ψ (T ·)`.
  have hkern : ∀ x : ℝ, ((m : ℝ) / smScale K T M₂) * psiSmooth ((m : ℝ) * x / smScale K T M₂)
      ≤ 4 * K * T * psiSmooth (T * x) := by
    intro x
    simpa only [smScale, mul_assoc] using rho_kernel_domination hT hK hM₂ hm x
  have hpt : ∀ u' : ℝ, f u' * (((m : ℝ) / smScale K T M₂) * psiSmooth ((m : ℝ) * (u - u') / smScale K T M₂))
      ≤ 4 * K * T * (psiSmooth (T * (u - u')) * f u') := by
    intro u'
    have h1 := mul_le_mul_of_nonneg_left (hkern (u - u')) (hfnn u')
    calc f u' * (((m : ℝ) / smScale K T M₂) * psiSmooth ((m : ℝ) * (u - u') / smScale K T M₂))
        ≤ f u' * (4 * K * T * psiSmooth (T * (u - u'))) := h1
      _ = 4 * K * T * (psiSmooth (T * (u - u')) * f u') := by ring
  -- Integrability of the majorant `4KT ψ(T(u-·)) f(·)`.
  have hcont : Continuous (fun u' : ℝ => psiSmooth (T * (u - u'))) :=
    psiSmooth_contDiff.continuous.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hIg : Integrable (fun u' : ℝ => psiSmooth (T * (u - u')) * f u') := by
    have := hf.mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (psiSmooth_nonneg _)]; exact hψle _)
    simpa [mul_comm] using this
  have hIg2 : Integrable (fun u' : ℝ => 4 * K * T * (psiSmooth (T * (u - u')) * f u')) :=
    hIg.const_mul _
  rw [gm, smoothed]
  have hstep : ∫ u', f u' * (((m : ℝ) / smScale K T M₂) * psiSmooth ((m : ℝ) * (u - u') / smScale K T M₂))
      ≤ ∫ u', 4 * K * T * (psiSmooth (T * (u - u')) * f u') :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u' => mul_nonneg (hfnn u')
        (mul_nonneg (div_nonneg hmpos.le hspos.le) (psiSmooth_nonneg _)))
      hIg2 (Filter.Eventually.of_forall hpt)
  refine le_trans hstep ?_
  rw [integral_const_mul]
  exact le_of_eq (by ring)

end

end Work.GM.Affine
