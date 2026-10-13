import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- Pointwise power bookkeeping: for `0 < t`,
`ε * t ^ (3/2) * t ^ (-p - 1) = ε * t ^ (1/2 - p)`. -/
private lemma mul_rpow_absorb {ε t p : ℝ} (ht : 0 < t) :
    ε * t ^ ((3 : ℝ) / 2) * t ^ (-p - 1) = ε * t ^ ((1 : ℝ) / 2 - p) := by
  rw [mul_assoc, ← Real.rpow_add ht]
  congr 1
  ring_nf

/-- **`rgB_int_Ioc`.**  If `|c t| ≤ ε t^{3/2}` for `0 < t ≤ δ` and `p > 3/2`, then
`t ↦ c t · t^{-p-1}` is integrable on `Ioc z δ`, for every `z > 0`.

The proof is a one-line domination: on `Ioc z δ` one has `z < t ≤ δ`, hence
`0 < t` and
`|c t · t^{-p-1}| ≤ ε t^{3/2} t^{-p-1} = ε t^{1/2 - p} ≤ ε z^{1/2 - p}`,
because `1/2 - p < 0` and `t ≥ z`.  The right-hand side is a constant, and `Ioc z δ`
has finite Lebesgue measure. -/
theorem rgB_int_Ioc {c : ℝ → ℝ} {p ε z δ : ℝ} (hp : 3 / 2 < p) (hε : 0 ≤ ε)
    (hz : 0 < z)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioc z δ) := by
  have hexp : (1 : ℝ) / 2 - p ≤ 0 := by linarith
  refine MeasureTheory.IntegrableOn.of_bound ?hfin ?hmeas' (ε * z ^ ((1 : ℝ) / 2 - p)) ?hbd
  · -- the interval `Ioc z δ` has finite measure
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · -- almost everywhere strong measurability
    have hsub : Set.Ioc z δ ⊆ Set.Ioi 0 := fun t ht => lt_trans hz ht.1
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
        (MeasureTheory.volume.restrict (Set.Ioc z δ)) := hmeas.mono_set hsub
    have hcont : ContinuousOn (fun t : ℝ => |t ^ (-p - 1)|) (Set.Ioc z δ) := by
      intro t ht
      exact (((Real.continuousAt_rpow_const t (-p - 1)
        (Or.inl (ne_of_gt (lt_trans hz ht.1))))).abs).continuousWithinAt
    have h2 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |t ^ (-p - 1)|)
        (MeasureTheory.volume.restrict (Set.Ioc z δ)) :=
      hcont.aestronglyMeasurable measurableSet_Ioc
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => |c t| * |t ^ (-p - 1)|)
        (MeasureTheory.volume.restrict (Set.Ioc z δ)) := h1.mul h2
    simpa only [Real.norm_eq_abs, abs_mul] using hprod
  · -- the pointwise domination on `Ioc z δ`
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_norm]
    obtain ⟨hzt, htδ⟩ := ht
    have ht0 : 0 < t := lt_trans hz hzt
    have htpow : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg ht0.le _
    have hct : |c t| ≤ ε * t ^ ((3 : ℝ) / 2) := hvy t ht0 htδ
    have hstep : ‖c t * t ^ (-p - 1)‖ ≤ ε * t ^ ((3 : ℝ) / 2) * t ^ (-p - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htpow]
      exact mul_le_mul_of_nonneg_right hct htpow
    have hzpow : t ^ ((1 : ℝ) / 2 - p) ≤ z ^ ((1 : ℝ) / 2 - p) :=
      Real.rpow_le_rpow_of_nonpos hz hzt.le hexp
    calc ‖c t * t ^ (-p - 1)‖
        ≤ ε * t ^ ((3 : ℝ) / 2) * t ^ (-p - 1) := hstep
      _ = ε * t ^ ((1 : ℝ) / 2 - p) := mul_rpow_absorb ht0
      _ ≤ ε * z ^ ((1 : ℝ) / 2 - p) := mul_le_mul_of_nonneg_left hzpow hε

end Work.FTS.PhiStar.Honesty
