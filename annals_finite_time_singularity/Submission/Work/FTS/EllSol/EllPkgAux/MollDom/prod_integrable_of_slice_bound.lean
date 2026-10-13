import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory

/-- If `k` vanishes outside `[-1,1]`, then multiplying by `|k (σ - t)|` can only see `Φ` on the
interval `[σ-1, σ+1]`. -/
private lemma abs_k_mul_eq_indicator {k : ℝ → ℝ} {Φ : ℝ → ℝ} {σ : ℝ}
    (hk0 : ∀ x : ℝ, 1 < |x| → k x = 0) (t : ℝ) :
    |k (σ - t)| * Φ t
      = |k (σ - t)| * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
  by_cases ht : t ∈ Set.Icc (σ - 1) (σ + 1)
  · rw [Set.indicator_of_mem ht]
  · have h1 : 1 < |σ - t| := by
      rw [Set.mem_Icc] at ht
      rcases not_and_or.mp ht with h | h
      · have hlt : t < σ - 1 := not_le.mp h
        rw [abs_of_pos (by linarith : (0 : ℝ) < σ - t)]; linarith
      · have hlt : σ + 1 < t := not_le.mp h
        rw [abs_of_neg (by linarith : σ - t < 0)]; linarith
    rw [Set.indicator_of_notMem ht, mul_zero, hk0 _ h1, abs_zero, zero_mul]

theorem prod_integrable_of_slice_bound {k : ℝ → ℝ} {w : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {M σ : ℝ}
    (hkm : Measurable k) (hkM : ∀ x : ℝ, |k x| ≤ M) (hk0 : ∀ x : ℝ, 1 < |x| → k x = 0)
    (hw_meas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hw_int : ∀ t : ℝ, MeasureTheory.IntegrableOn (fun s : ℝ => w t s) Work.Spaces.Iθ)
    (hw_bd : ∀ t : ℝ, ∫ s in Work.Spaces.Iθ, |w t s| ≤ Φ t)
    (hΦ_int : MeasureTheory.IntegrableOn Φ (Set.Icc (σ - 1) (σ + 1))) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => k (σ - p.1) * w p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  -- `M` is nonnegative and `Φ` is nonnegative (it dominates a nonnegative integral)
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (k 0)) (hkM 0)
  have hΦnn : ∀ t : ℝ, 0 ≤ Φ t := fun t =>
    le_trans (integral_nonneg (f := fun s : ℝ => |w t s|) (fun s => abs_nonneg _)) (hw_bd t)
  -- the dominating `z`-marginal: `M · Φ` cut down to the support interval
  have hDind : Integrable (Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ) volume :=
    hΦ_int.integrable_indicator measurableSet_Icc
  have hDint : Integrable
      (fun t : ℝ => M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t) volume :=
    hDind.const_mul M
  -- pointwise bound of the norm of each slice
  have hpt : ∀ t : ℝ, ‖∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)‖
      ≤ M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
    intro t
    have hnn : 0 ≤ ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ) :=
      integral_nonneg (fun s => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)
        = ∫ s in Work.Spaces.Iθ, |k (σ - t)| * |w t s| := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
          simp only [Real.norm_eq_abs, abs_mul]
      _ = |k (σ - t)| * ∫ s in Work.Spaces.Iθ, |w t s| := integral_const_mul _ _
      _ ≤ |k (σ - t)| * Φ t := mul_le_mul_of_nonneg_left (hw_bd t) (abs_nonneg _)
      _ ≤ M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
          rw [abs_k_mul_eq_indicator hk0 t]
          exact mul_le_mul_of_nonneg_right (hkM _)
            (Set.indicator_nonneg (fun a _ => hΦnn a) t)
  -- joint measurability of the integrand
  have hkm2 : Measurable (fun p : ℝ × ℝ => k (σ - p.1)) :=
    hkm.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => σ - p.1))
  have hsm : AEStronglyMeasurable (fun p : ℝ × ℝ => k (σ - p.1) * w p.1 p.2)
      (volume.prod (volume.restrict Work.Spaces.Iθ)) :=
    hkm2.aestronglyMeasurable.mul hw_meas
  -- measurability of the `z`-marginal
  have hnm : AEStronglyMeasurable
      (fun t : ℝ => ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)) volume :=
    hsm.norm.integral_prod_right'
  -- integrability of the `z`-marginal
  have hmarg : Integrable
      (fun t : ℝ => ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)) volume :=
    Integrable.mono' hDint hnm (Filter.Eventually.of_forall hpt)
  -- Fubini
  exact (integrable_prod_iff hsm).mpr
    ⟨Filter.Eventually.of_forall (fun t => (hw_int t).const_mul (k (σ - t))), hmarg⟩

end Work.FTS.EllSol.EllPkgAux.MollDom
