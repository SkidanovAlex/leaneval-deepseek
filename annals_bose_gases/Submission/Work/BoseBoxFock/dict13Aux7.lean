import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dict13Aux4
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux7` — the box `L¹` norm and the truncation limit

`boxL1 ℓ e` (`dict13Aux4`) is the iterated `∫⁻∫⁻` of `‖e‖` over the cube square.  Here we record

* its monotonicity in `e`,
* its identification with the ordinary integral of `‖uncurry e‖` over the *restricted* product
  measure (`boxL1_toReal_eq_integral`, Tonelli + `integral_eq_lintegral_of_nonneg_ae`),
* the truncation limit `boxL1 ℓ (H - trunc N H) → 0` (`boxL1_trunc_tendsto`, dominated convergence
  on that restricted product).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The restricted box cube measure is bounded by the ambient volume. -/
theorem restrict_acube_le (ℓ : ℝ) :
    ((volume : Measure E3).restrict (acb ℓ)) ≤ (volume : Measure E3) :=
  Measure.restrict_le_self

/-- The restricted product measure on `Λ × Λ` is bounded by the ambient product measure. -/
theorem prod_restrict_acube_le (ℓ : ℝ) :
    (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))
      ≤ ((volume : Measure E3).prod (volume : Measure E3)) :=
  Measure.prod_mono (restrict_acube_le ℓ) (restrict_acube_le ℓ)

/-- `boxL1` is monotone in the pointwise norm of the kernel. -/
theorem boxL1_mono {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ} (h : ∀ a b, ‖e₁ a b‖ ≤ ‖e₂ a b‖) :
    boxL1 ℓ e₁ ≤ boxL1 ℓ e₂ := by
  refine lintegral_mono (fun a => lintegral_mono (fun b => ?_))
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h a b)

/-- The box `L¹` norm, as an ordinary integral of `‖uncurry e‖` over the restricted product. -/
theorem boxL1_toReal_eq_integral {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3))) :
    (boxL1 ℓ e).toReal
      = ∫ p, ‖Function.uncurry e p‖
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))) := by
  have hac : AEStronglyMeasurable (Function.uncurry e)
      (((volume : Measure E3).restrict (acb ℓ)).prod
        ((volume : Measure E3).restrict (acb ℓ))) := he.mono_measure (prod_restrict_acube_le ℓ)
  have h1 : boxL1 ℓ e
      = ∫⁻ p, ‖Function.uncurry e p‖ₑ
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))) := by
    rw [boxL1]
    exact (lintegral_prod (fun p : E3 × E3 => ‖Function.uncurry e p‖ₑ)
      hac.aemeasurable.enorm).symm
  rw [h1]
  have h2 : (∫⁻ p, ‖Function.uncurry e p‖ₑ
        ∂(((volume : Measure E3).restrict (acb ℓ)).prod
          ((volume : Measure E3).restrict (acb ℓ)))).toReal
      = ∫ p, ‖Function.uncurry e p‖
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))) := by
    have hcongr : (∫⁻ p, ‖Function.uncurry e p‖ₑ
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))))
        = ∫⁻ p, ENNReal.ofReal ‖Function.uncurry e p‖
            ∂(((volume : Measure E3).restrict (acb ℓ)).prod
              ((volume : Measure E3).restrict (acb ℓ))) :=
      lintegral_congr fun p => (ofReal_norm _).symm
    rw [hcongr, ← integral_eq_lintegral_of_nonneg_ae
      (μ := ((volume : Measure E3).restrict (acb ℓ)).prod
        ((volume : Measure E3).restrict (acb ℓ)))
      (Filter.Eventually.of_forall (fun p => norm_nonneg _)) hac.norm]
  exact h2

/-- Measurability of the value truncation. -/
theorem measurable_trunc {H : E3 → E3 → ℝ} (hm : Measurable (Function.uncurry H)) (N : ℕ) :
    Measurable (Function.uncurry (trunc N H)) := by
  rw [show Function.uncurry (trunc N H)
      = fun p : E3 × E3 => if ‖Function.uncurry H p‖ ≤ (N : ℝ)
          then Function.uncurry H p else 0 from rfl]
  exact Measurable.ite (measurableSet_le hm.norm measurable_const) hm measurable_const

/-- Measurability of the truncated difference. -/
theorem measurable_trunc_sub {H : E3 → E3 → ℝ} (hm : Measurable (Function.uncurry H)) (N : ℕ) :
    Measurable (Function.uncurry (fun a b => H a b - trunc N H a b)) := by
  have h1 : Measurable (Function.uncurry (trunc N H)) := by
    rw [show Function.uncurry (trunc N H)
        = fun p : E3 × E3 => if ‖Function.uncurry H p‖ ≤ (N : ℝ)
            then Function.uncurry H p else 0 from rfl]
    exact Measurable.ite (measurableSet_le hm.norm measurable_const) hm measurable_const
  rw [show Function.uncurry (fun a b => H a b - trunc N H a b)
      = fun p : E3 × E3 => Function.uncurry H p - Function.uncurry (trunc N H) p from rfl]
  exact hm.sub h1

/-- **The truncation limit of the box `L¹` norm**: `∫∫_{Λ×Λ}‖H − trunc N H‖ → 0`. -/
theorem boxL1_trunc_tendsto {ℓ : ℝ} {H : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry H)) (hi : boxL1 ℓ H < ⊤) :
    Filter.Tendsto
      (fun N : ℕ => (boxL1 ℓ (fun a b => H a b - trunc N H a b)).toReal)
      Filter.atTop (nhds 0) := by
  have hle := prod_restrict_acube_le ℓ
  have hac : AEStronglyMeasurable (fun p : E3 × E3 => ‖Function.uncurry H p‖)
      (((volume : Measure E3).restrict (acb ℓ)).prod
        ((volume : Measure E3).restrict (acb ℓ))) :=
    (hm.aestronglyMeasurable.mono_measure hle).norm
  have hInt : Integrable (fun p : E3 × E3 => ‖Function.uncurry H p‖)
      (((volume : Measure E3).restrict (acb ℓ)).prod
        ((volume : Measure E3).restrict (acb ℓ))) := by
    refine ⟨hac, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have hcongr : (∫⁻ a : E3 × E3, ENNReal.ofReal ‖‖Function.uncurry H a‖‖
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))))
        = ∫⁻ a, ‖Function.uncurry H a‖ₑ
            ∂(((volume : Measure E3).restrict (acb ℓ)).prod
              ((volume : Measure E3).restrict (acb ℓ))) := by
      refine lintegral_congr fun a => ?_
      rw [Real.norm_of_nonneg (norm_nonneg _), ofReal_norm]
    rw [hcongr, lintegral_prod (fun p : E3 × E3 => ‖Function.uncurry H p‖ₑ)
        ((hm.aestronglyMeasurable.mono_measure hle).aemeasurable.enorm)]
    simpa only [boxL1, Function.uncurry] using hi
  have hconv : Filter.Tendsto
      (fun N : ℕ => ∫ p, ‖Function.uncurry (fun a b => H a b - trunc N H a b) p‖
        ∂(((volume : Measure E3).restrict (acb ℓ)).prod
          ((volume : Measure E3).restrict (acb ℓ)))) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto
        (fun N : ℕ => ∫ p, ‖Function.uncurry (fun a b => H a b - trunc N H a b) p‖
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))))
        Filter.atTop (nhds (∫ _p : E3 × E3, (0 : ℝ)
          ∂(((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ))))) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := ((volume : Measure E3).restrict (acb ℓ)).prod
          ((volume : Measure E3).restrict (acb ℓ)))
        (F := fun N p => ‖Function.uncurry (fun a b => H a b - trunc N H a b) p‖)
        (f := fun _ => 0) (bound := fun p => ‖Function.uncurry H p‖) (fun N => ?_) hInt
        (fun N => ?_) ?_
      · exact (measurable_trunc_sub hm N).aestronglyMeasurable.norm.mono_measure le_rfl
      · filter_upwards with p
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        show ‖Function.uncurry H p - Function.uncurry (trunc N H) p‖ ≤ ‖Function.uncurry H p‖
        have h := trunc_sub_abs N H p.1 p.2
        simp only [Function.uncurry] at h ⊢
        rw [h]
        split_ifs with hh
        · exact norm_nonneg _
        · exact le_rfl
      · refine Filter.Eventually.of_forall (fun p => ?_)
        have hev : ∀ᶠ N : ℕ in Filter.atTop, ‖H p.1 p.2‖ ≤ (N : ℝ) :=
          Filter.eventually_atTop.mpr ⟨⌈‖H p.1 p.2‖⌉₊, fun N hN => by
            exact le_trans (Nat.le_ceil _) (by exact_mod_cast hN)⟩
        have heq : (fun _ : ℕ => (0 : ℝ))
            =ᶠ[Filter.atTop]
            fun N : ℕ => ‖Function.uncurry (fun a b => H a b - trunc N H a b) p‖ := by
          filter_upwards [hev] with N hN
          have htr : Function.uncurry (trunc N H) p = Function.uncurry H p := by
            simp only [Function.uncurry, trunc_apply]
            exact if_pos hN
          rw [show Function.uncurry (fun a b => H a b - trunc N H a b) p
              = Function.uncurry H p - Function.uncurry (trunc N H) p from rfl, htr, sub_self,
            norm_zero]
        exact Filter.Tendsto.congr' heq tendsto_const_nhds
    simpa using h0
  refine hconv.congr' ?_
  filter_upwards with N
  exact (boxL1_toReal_eq_integral (e := fun a b => H a b - trunc N H a b)
    (measurable_trunc_sub hm N).aestronglyMeasurable).symm

end Work.BoseBoxFock
