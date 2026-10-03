import Mathlib
import Submission.Work.Pert.V5.integral_inv_max_le
import Submission.Work.Pert.V5.inv_norm_le_inv_max

/-!
# `Work.Pert.V5.line_integral_inv_norm_le`

The elementary line-integral bound used by the V5 deviation assembly (Shishikura's
`∫ dt / |r + t v| ≤ 2 (1 + log (2 + ℓ/δ))`, `‖v‖ = 1`, `|r + t v| ≥ δ` on `[0,ℓ]`).

Fix `t₀ := -Re(conj v * r)`, the (real) minimiser of `t ↦ ‖r + t v‖` (here `‖v‖ = 1`, so
`‖r + t v‖² = (t - t₀)² + Im(conj v * r)²`), and let `tc` be its orthogonal projection onto
`[0,ℓ]`.  Then for `t ∈ [0,ℓ]`:

* `δ ≤ ‖r + t v‖` by hypothesis, and
* `|t - tc| ≤ |t - t₀| ≤ |Re(conj v * (r + t v))| ≤ ‖r + t v‖`,

so `max δ |t - tc| ≤ ‖r + t v‖`, i.e. `1/‖r + t v‖ ≤ 1/max δ |t - tc|`
(`Work.Pert.V5.inv_norm_le_inv_max`, applied pointwise).

`t ↦ 1/max δ |t - tc|` is continuous with `max δ |t - tc| ≥ δ > 0`, hence interval integrable;
monotonicity of the integral (`intervalIntegral.integral_mono_on`) and the model estimate
`Work.Pert.V5.integral_inv_max_le` finish the proof.
-/

open MeasureTheory

namespace Work.Pert.V5

noncomputable section

theorem line_integral_inv_norm_le {r v : ℂ} {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ)
    (hv : ‖v‖ = 1)
    (h : ∀ t ∈ Set.Icc (0:ℝ) ℓ, δ ≤ ‖r + (t : ℂ) • v‖) :
    ∫ t in (0:ℝ)..ℓ, 1 / ‖r + (t : ℂ) • v‖ ≤ 2 * (1 + Real.log (2 + ℓ / δ)) := by
  have htc : min (max (-(star v * r).re) 0) ℓ ∈ Set.Icc (0:ℝ) ℓ :=
    ⟨le_min (le_max_right _ _) hℓ, min_le_right _ _⟩
  have hcont1 : Continuous (fun t : ℝ => r + (t : ℂ) • v) := by fun_prop
  have hf : IntervalIntegrable (fun t : ℝ => 1 / ‖r + (t : ℂ) • v‖) volume (0:ℝ) ℓ := by
    rw [show (fun t : ℝ => 1 / ‖r + (t : ℂ) • v‖)
          = (fun t : ℝ => (‖r + (t : ℂ) • v‖)⁻¹) from by funext t; rw [one_div]]
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?_ ?_
    · exact hcont1.norm.continuousOn
    · intro t ht
      rw [Set.uIcc_of_le hℓ] at ht
      exact ne_of_gt (lt_of_lt_of_le hδ (h t ht))
  have hg : IntervalIntegrable
      (fun t : ℝ => 1 / max δ |t - min (max (-(star v * r).re) 0) ℓ|) volume (0:ℝ) ℓ := by
    rw [show (fun t : ℝ => 1 / max δ |t - min (max (-(star v * r).re) 0) ℓ|)
          = (fun t : ℝ => (max δ |t - min (max (-(star v * r).re) 0) ℓ|)⁻¹) from by
            funext t; rw [one_div]]
    refine Continuous.intervalIntegrable ?_ 0 ℓ
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro t
      exact ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _))
  calc ∫ t in (0:ℝ)..ℓ, 1 / ‖r + (t : ℂ) • v‖
      ≤ ∫ t in (0:ℝ)..ℓ, 1 / max δ |t - min (max (-(star v * r).re) 0) ℓ| :=
        intervalIntegral.integral_mono_on hℓ hf hg (inv_norm_le_inv_max hℓ hδ hv h)
    _ ≤ 2 * (1 + Real.log (2 + ℓ / δ)) := integral_inv_max_le hℓ hδ htc

end

end Work.Pert.V5
