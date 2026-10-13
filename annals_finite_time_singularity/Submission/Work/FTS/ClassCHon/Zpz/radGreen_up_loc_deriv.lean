import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter
open scoped Topology

/-- **Local integrability of the radial derivative, away from `0`.**

If `t ↦ t * deriv c t * t ^ (q - 1)` is integrable on `(0,1)` (with `0 < q`), then
`t ↦ deriv c t * t ^ (-p)` is integrable on `(z,1)` for every `z > 0` (with `0 ≤ p`).

Indeed, on `(z,1)` we have `t ≥ z > 0`, so
`|deriv c t * t ^ (-p)| = |deriv c t| * t ^ (-(p+q)) * t ^ q
  ≤ z ^ (-(p+q)) * |t * deriv c t * t ^ (q-1)|`
(because `t ^ q = t * t ^ (q-1)` and `t ↦ t ^ (-(p+q))` is antitone on `(0,∞)` as `-(p+q) ≤ 0`),
and the dominating function is integrable on `(z,1) ⊆ (0,1)`. -/
lemma radGreen_up_loc_deriv {c : ℝ → ℝ} {p q z : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hz : 0 < z)
    (hd0 : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (q - 1)) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioo z 1) := by
  have hsub : Set.Ioo z 1 ⊆ Set.Ioo (0 : ℝ) 1 := fun t ht => ⟨lt_trans hz ht.1, ht.2⟩
  -- the dominating function is integrable on `(z,1)`
  have hd0' : Integrable (fun t : ℝ => t * deriv c t * t ^ (q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hd0
  have h1 : Integrable (fun t : ℝ => t * deriv c t * t ^ (q - 1))
      (volume.restrict (Set.Ioo z 1)) :=
    Integrable.mono_measure hd0' (Measure.restrict_mono hsub le_rfl)
  have h2 : Integrable (fun t : ℝ => z ^ (-(p + q)) * |t * deriv c t * t ^ (q - 1)|)
      (volume.restrict (Set.Ioo z 1)) :=
    h1.abs.const_mul (z ^ (-(p + q)))
  refine Integrable.mono' (μ := volume.restrict (Set.Ioo z 1))
    (f := fun t : ℝ => deriv c t * t ^ (-p))
    (g := fun t : ℝ => z ^ (-(p + q)) * |t * deriv c t * t ^ (q - 1)|) h2 ?_ ?_
  · -- a.e. strong measurability: replace `t ^ (-p)` by its `exp/log` form
    have hF : Measurable (fun t : ℝ => deriv c t * Real.exp (-p * Real.log t)) :=
      (measurable_deriv c).mul
        (Real.measurable_exp.comp
          ((measurable_const : Measurable fun _ : ℝ => -p).mul Real.measurable_log))
    refine AEStronglyMeasurable.congr hF.aestronglyMeasurable ?_
    have heq : ∀ᵐ t ∂(volume.restrict (Set.Ioo z 1)),
        deriv c t * Real.exp (-p * Real.log t) = deriv c t * t ^ (-p) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with t ht
      have ht0 : 0 < t := lt_trans hz ht.1
      rw [Real.rpow_def_of_pos ht0]
      rw [show -p * Real.log t = Real.log t * (-p) by ring]
    exact heq
  · -- the pointwise bound, a.e. in `(z,1)`
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    have ht0 : 0 < t := lt_trans hz ht.1
    have hexp : t ^ (-p) = t ^ (-(p + q)) * t ^ q := by
      have h := Real.rpow_add ht0 (-(p + q)) q
      rw [show -(p + q) + q = -p by ring] at h
      exact h
    have hq1 : t ^ q = t * t ^ (q - 1) := by
      have h := Real.rpow_add ht0 1 (q - 1)
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) + (q - 1) = q by ring] at h
      exact h
    have hle : t ^ (-p) ≤ z ^ (-(p + q)) * (t * t ^ (q - 1)) := by
      rw [hexp, hq1]
      refine mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hz (le_of_lt ht.1) (by linarith)) ?_
      exact le_of_lt (mul_pos ht0 (Real.rpow_pos_of_pos ht0 (q - 1)))
    calc ‖deriv c t * t ^ (-p)‖
        = |deriv c t| * t ^ (-p) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 (-p))]
      _ ≤ |deriv c t| * (z ^ (-(p + q)) * (t * t ^ (q - 1))) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = z ^ (-(p + q)) * |t * deriv c t * t ^ (q - 1)| := by
          rw [abs_mul, abs_mul, abs_of_pos ht0,
            abs_of_pos (Real.rpow_pos_of_pos ht0 (q - 1))]
          ring

end Work.FTS.ClassCHon.Zpz
