import Mathlib.Analysis.Convolution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uvSmear_L1_le`

The **uniform-in-`Λ` `L¹` bound** for the UV smearing `uvSmear fu Λ f = uvKernel fu Λ ⋆ f`:
there is a constant `C ≥ 0`, depending on the low-cut profile `fu` only, with

    `∫ x, ‖uvSmear fu Λ f x‖ ≤ C · ∫ x, ‖f x‖`     for all `Λ > 0` and all `f ∈ L¹(ℝ³)`.

This is the classical Young inequality `‖K ⋆ f‖₁ ≤ ‖K‖₁ ‖f‖₁` for a convolution kernel, with the
single content that `‖uvKernel fu Λ‖₁` is bounded **uniformly in `Λ`**: that is the delegated
lemma `uvKernel_L1_bound_of_decay`, fed by the scaled Schwartz decay `uvKernel_decay`
(`‖uvKernel fu Λ z‖ ≤ C Λ³ (1 + Λ‖z‖)^{-5}`, i.e. the `z ↦ Λz` rescaling of the fixed integrable
profile `C (1 + ‖z‖)^{-5}`).

## Proof

Write `K = uvKernel fu Λ`.  Since `uvSmear fu Λ f x = ∫ t, K t * f (x − t)`
(`integral_sub_left_eq_self`), the triangle inequality for the Bochner integral gives, pointwise,

    `‖uvSmear fu Λ f x‖ ≤ ∫ t, ‖K t‖ ‖f (x − t)‖`,

so `∫ x, ‖uvSmear fu Λ f x‖ ≤ ∫ x, ∫ t, ‖K t‖ ‖f (x − t)‖` by monotonicity of the integral.  The
joint integrand `(x,t) ↦ ‖K t‖ ‖f (x − t)‖` is integrable on the product (`Integrable.convolution_integrand`
applied to `‖K‖ ∈ L¹` and `‖f‖ ∈ L¹`), so Fubini (`integral_integral_swap`) turns the iterated
integral into `∫ t, ‖K t‖ ∫ x, ‖f (x − t)‖`, and translation invariance of Lebesgue measure
(`integral_sub_right_eq_self`) makes the inner integral equal to `‖f‖₁`.  The result is
`‖K‖₁ · ‖f‖₁ ≤ M · ‖f‖₁`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem uvSmear_L1_le (fu : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : ℝ}, 0 < Λ → ∀ {f : EuclideanSpace ℝ (Fin 3) → ℝ},
      MeasureTheory.Integrable f →
      ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.uvSmear fu Λ f x‖
        ≤ C * ∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ := by
  obtain ⟨C₀, hC₀nn, hdec⟩ := uvKernel_decay fu 5
  obtain ⟨M, hMnn, hM⟩ := uvKernel_L1_bound_of_decay fu hC₀nn hdec
  refine ⟨M, hMnn, ?_⟩
  intro Λ hΛ f hf
  have hKint : Integrable (uvKernel fu Λ) := integrable_uvKernel fu hΛ
  have hKnorm : Integrable (fun t : E3 => ‖uvKernel fu Λ t‖) := hKint.norm
  -- integrability of the joint integrand `(x,t) ↦ ‖K t‖ ‖f (x - t)‖`
  have hjoint : Integrable (fun p : E3 × E3 => ‖uvKernel fu Λ p.2‖ * ‖f (p.1 - p.2)‖)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    Integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hKnorm hf.norm
  set G : E3 → ℝ := fun x => ∫ t : E3, ‖uvKernel fu Λ t‖ * ‖f (x - t)‖ with hG
  have hGint : Integrable G := hjoint.integral_prod_left
  -- step 1: the pointwise triangle inequality, integrated
  have hstep1 : ∫ x : E3, ‖uvSmear fu Λ f x‖ ≤ ∫ x : E3, G x := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGint
      (Filter.Eventually.of_forall fun x => ?_)
    change ‖uvSmear fu Λ f x‖ ≤ G x
    have hsub : uvSmear fu Λ f x = ∫ t : E3, uvKernel fu Λ t * f (x - t) := by
      rw [uvSmear]
      simpa only [sub_sub_cancel] using
        integral_sub_left_eq_self (fun t : E3 => uvKernel fu Λ t * f (x - t)) volume x
    rw [hsub]
    calc ‖∫ t : E3, uvKernel fu Λ t * f (x - t)‖
        ≤ ∫ t : E3, ‖uvKernel fu Λ t * f (x - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t : E3, ‖uvKernel fu Λ t‖ * ‖f (x - t)‖ := by
          apply integral_congr_ae
          filter_upwards with t
          rw [norm_mul]
      _ = G x := rfl
  -- step 2: Fubini and translation invariance of Lebesgue measure
  have hswap : ∫ x : E3, G x = ∫ t : E3, ∫ x : E3, ‖uvKernel fu Λ t‖ * ‖f (x - t)‖ := by
    rw [hG]
    exact integral_integral_swap hjoint
  have hstep2 : ∫ x : E3, G x = ∫ t : E3, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f x‖) := by
    rw [hswap]
    apply integral_congr_ae
    filter_upwards with t
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun y : E3 => ‖f y‖) t
  -- step 3: `∫ t, ‖K t‖ · ‖f‖₁ = ‖K‖₁ · ‖f‖₁ ≤ M · ‖f‖₁`
  have hstep3 : (∫ t : E3, ‖uvKernel fu Λ t‖ * (∫ x : E3, ‖f x‖))
      = (∫ t : E3, ‖uvKernel fu Λ t‖) * (∫ x : E3, ‖f x‖) :=
    integral_mul_const _ _
  rw [hstep2, hstep3] at hstep1
  exact hstep1.trans
    (mul_le_mul_of_nonneg_right (hM Λ hΛ) (integral_nonneg fun _ => norm_nonneg _))

end Work.BoseBoxFock
