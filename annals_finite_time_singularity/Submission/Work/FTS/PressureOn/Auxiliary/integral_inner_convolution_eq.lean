/-
# Self-adjointness of convolution by an even kernel (inner-product form)

`Work.FTS.PressureOn.Auxiliary.integral_inner_convolution_eq`:

  `∫ x, ⟪Φ x, (ρ ⋆ f) x⟫ = ∫ x, ⟪(ρ ⋆ Φ) x, f x⟫`

for continuous `Φ, f : ℝ³ → ℝ³` with `f` compactly supported and a continuous, compactly
supported, *even* kernel `ρ : ℝ³ → ℝ`, where `⋆` is the scalar convolution
`(ρ ⋆ f) x = ∫ t, ρ t • f (x - t)` (`MeasureTheory.convolution ρ f (lsmul ℝ ℝ) volume`).

## Mathematics

Unfold the convolutions and the inner products: the identity says that the double integrals

  `∫∫ ρ t ⟪Φ x, f (x - t)⟫ dx dt`   and   `∫∫ ρ t ⟪Φ (x - t), f x⟫ dx dt`

agree.  Fubini (with the two given product-integrability hypotheses `hα`, `hβ`) reduces both to
an iterated integral in the order `dt dx`; for the first one the inner change of variables
`x ↦ x + t` (translation invariance of Lebesgue measure) gives `∫∫ ρ t ⟪Φ (x + t), f x⟫`, and for
the second one the outer change of variables `t ↦ -t` (negation invariance, using `ρ (-t) = ρ t`)
gives the same integral.

## Formal route

* `hpt1`, `hpt2`: pull the inner product out of the Bochner integral with
  `ContinuousLinearMap.integral_comp_comm` applied to `innerSL ℝ ·` (the integrand `t ↦ ρ t • f (x-t)`
  is integrable because `ρ` is continuous with compact support), then use
  `real_inner_smul_right` / `real_inner_comm`.
* `key2`, `key45`: Fubini, `integral_integral_swap`, from `hα` resp. `hβ`.
* `key3`: translation invariance in the inner variable, `integral_add_right_eq_self`.
* `key4`: negation invariance of the outer integral, `integral_neg_eq_self`, plus evenness of `ρ`.
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

theorem integral_inner_convolution_eq
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hΦ : Continuous Φ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (heven : ∀ z, ρ (-z) = ρ z)
    (hα : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        ρ t * inner ℝ (Φ x) (f (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hβ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        ρ t * inner ℝ (Φ (x - t)) (f x)) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    ∫ x, inner ℝ (Φ x)
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) := by
  -- Step 1: unfold the convolution and pull the inner product inside the integral.
  have hpt1 : ∀ x, inner ℝ (Φ x)
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)) := by
    intro x
    have hint : Integrable (fun t : EuclideanSpace ℝ (Fin 3) => ρ t • f (x - t)) :=
      (hf.comp (continuous_const.sub continuous_id)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        hρ hρc
    have hkey : (innerSL ℝ (Φ x)) (∫ t, ρ t • f (x - t))
        = ∫ t, (innerSL ℝ (Φ x)) (ρ t • f (x - t)) :=
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (Φ x)) hint).symm
    rw [MeasureTheory.convolution_lsmul]
    rw [← innerSL_apply_apply, hkey]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [innerSL_apply_apply, real_inner_smul_right]
  have hpt2 : ∀ x, inner ℝ
      (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      (f x) = ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x) := by
    intro x
    have hint : Integrable (fun t : EuclideanSpace ℝ (Fin 3) => ρ t • Φ (x - t)) :=
      (hΦ.comp (continuous_const.sub continuous_id)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        hρ hρc
    have hkey : (innerSL ℝ (f x)) (∫ t, ρ t • Φ (x - t))
        = ∫ t, (innerSL ℝ (f x)) (ρ t • Φ (x - t)) :=
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (f x)) hint).symm
    rw [MeasureTheory.convolution_lsmul, real_inner_comm]
    rw [← innerSL_apply_apply, hkey]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
  -- Now the chain of identities between iterated integrals.
  have key1 : ∫ x, inner ℝ (Φ x)
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hpt1 x
  -- Fubini (from `hα`).
  have key2 : (∫ x, ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ x) (f (x - t)) :=
    MeasureTheory.integral_integral_swap hα
  -- Translate the inner variable: `x ↦ x + t`.
  have key3 : (∫ t, ∫ x, ρ t * inner ℝ (Φ x) (f (x - t)))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simpa using (MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun y : EuclideanSpace ℝ (Fin 3) => ρ t * inner ℝ (Φ y) (f (y - t))) t).symm
  have h1 : ∀ t, (∫ x, ρ t * inner ℝ (Φ (x + t)) (f x))
      = ∫ x, ρ (-t) * inner ℝ (Φ (x - (-t))) (f x) := by
    intro t
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [← heven t, sub_neg_eq_add]
  -- `t ↦ -t` in the outer integral, using that `ρ` is even.
  have key4 : (∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x) := by
    calc ∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x)
        = ∫ t, ∫ x, ρ (-t) * inner ℝ (Φ (x - (-t))) (f x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          exact h1 t
      _ = ∫ t, (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) (-t) := rfl
      _ = ∫ t, (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) t :=
          MeasureTheory.integral_neg_eq_self
            (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) MeasureTheory.volume
      _ = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x) := rfl
  -- Fubini in the other direction (from `hβ`).
  have key45 : (∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x))
      = ∫ x, ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x) :=
    (MeasureTheory.integral_integral_swap hβ).symm
  have key5 : (∫ x, ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x))
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact (hpt2 x).symm
  exact key1.trans (key2.trans (key3.trans (key4.trans (key45.trans key5))))

end Work.FTS.PressureOn.Auxiliary
