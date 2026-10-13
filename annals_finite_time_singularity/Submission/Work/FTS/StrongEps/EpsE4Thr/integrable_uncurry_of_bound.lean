import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.EpsE4Thr

theorem integrable_uncurry_of_bound {f : ℝ → ℝ × ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hfm : AEMeasurable (Function.uncurry f) (MeasureTheory.volume.prod diaM))
    (hfnn : 0 ≤ᵐ[MeasureTheory.volume.prod diaM] Function.uncurry f)
    (hint : ∀ σ ∈ Set.Icc a b, MeasureTheory.Integrable (fun p => f σ p) diaM)
    (hbd : ∀ σ ∈ Set.Icc a b, ∫ p, f σ p ∂diaM ≤ K) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) := by
  -- The `σ`-measure is finite, so `Integrable` follows from a.e. bounds.
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  -- Restricting `σ` to `(a,b]` only lowers the product measure.
  have hle : ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM)
      ≤ MeasureTheory.volume.prod diaM :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have h1f : AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) :=
    (hfm.mono_measure hle).aestronglyMeasurable
  -- Slicewise integrability holds for every `σ ∈ (a,b]`, hence a.e.
  have hint_ae : ∀ᵐ σ ∂((MeasureTheory.volume.restrict (Set.Ioc a b)) : Measure ℝ),
      Integrable (fun p => f σ p) diaM := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun σ hσ => hint σ (Set.Ioc_subset_Icc_self hσ)
  -- A.e. nonnegativity of the slices, transferred from the product measure.
  have hnnμ : ∀ᵐ σ ∂((MeasureTheory.volume.restrict (Set.Ioc a b)) : Measure ℝ),
      ∀ᵐ p ∂diaM, 0 ≤ f σ p :=
    (ae_mono Measure.restrict_le_self) (Measure.ae_ae_of_ae_prod hfnn)
  -- The slicewise integral bound, for a.e. `σ`.
  have hbd_ae : ∀ᵐ σ ∂((MeasureTheory.volume.restrict (Set.Ioc a b)) : Measure ℝ),
      ∫ p, f σ p ∂diaM ≤ K := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun σ hσ => hbd σ (Set.Ioc_subset_Icc_self hσ)
  rw [integrable_prod_iff h1f]
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry_apply_pair] using hint_ae
  · -- The norm of the slice integral is dominated by `max K 0` a.e.
    refine Integrable.mono' (integrable_const (max K 0)) h1f.norm.integral_prod_right' ?_
    filter_upwards [hint_ae, hnnμ, hbd_ae] with σ hintσ hnnσ hbdσ
    have h1 : ‖∫ p, ‖Function.uncurry f (σ, p)‖ ∂diaM‖
        = ∫ p, ‖Function.uncurry f (σ, p)‖ ∂diaM := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall fun p => norm_nonneg _))]
    rw [h1]
    have h2 : ∫ p, ‖Function.uncurry f (σ, p)‖ ∂diaM
        = ∫ p, f σ p ∂diaM :=
      integral_congr_ae (hnnσ.mono fun p hp => by
        simp only [Real.norm_eq_abs, Function.uncurry_apply_pair]
        exact abs_of_nonneg hp)
    rw [h2]
    exact le_trans hbdσ (le_max_left K 0)

end Work.FTS.StrongEps.EpsE4Thr
