/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `sin (2θ) ^ c` on the flat angular interval

The function `θ ↦ sin (2 θ) ^ c` is integrable on `(0, π/2)` exactly when `c > -1`:
the two singularities at `θ = 0` and `θ = π/2` are of power type, and Jordan's
inequality `(2/π) y ≤ sin y` on `[0, π/2]` turns the weight into
`(π/4) ^ (-c) * (θ ^ (-c) + (π/2 - θ) ^ (-c))`, which is integrable precisely for
`-1 < c` (the workspace lemmas `Spaces.sin_rpow_le_majorant` and
`Spaces.integrableOn_majorant_rpow` provide exactly this comparison).
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Flat

open MeasureTheory Set
open scoped Real

/-- `sin (2θ) ^ c` is integrable on the closed interval `[0, π/2]` when `-1 < c`.

On `[0, π/2]` the weight vanishes only at the endpoints (a null set), so it suffices
to dominate it there: for `c ≥ 0` it is bounded by `1`, and for `c < 0` by the explicit
integrable majorant `(π/4) ^ (-c) * (θ ^ (-c) + (π/2 - θ) ^ (-c))`. -/
theorem integrableOn_sin_two_rpow_Icc {c : ℝ} (hc : -1 < c) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))) :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const c).aestronglyMeasurable
  have hsin0 : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  by_cases hc0 : 0 ≤ c
  · -- nonnegative exponent: bounded by the integrable constant `1`
    refine Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Icc (0 : ℝ) (Real.pi / 2))
        (C := (1 : ℝ)) ?_) hmeas ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 c)]
      exact Real.rpow_le_one h0 (Real.sin_le_one (2 * θ)) hc0
  · -- negative exponent: Jordan's inequality gives an explicit `rpow` majorant
    have hcneg : c < 0 := not_le.mp hc0
    have hp0 : 0 < -c := by linarith
    have hp1 : -c < 1 := by linarith
    refine Integrable.mono'
      (Work.Spaces.integrableOn_majorant_rpow (-c) hp0 hp1) hmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have h0 := hsin0 θ hθ
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 c)]
    simpa using Work.Spaces.sin_rpow_le_majorant (-c) θ hp0 hθ

theorem integrableOnSinTwoRpow {c : ℝ} (hc : -1 < c) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (integrableOn_sin_two_rpow_Icc hc).mono_set fun _ hx =>
    ⟨hx.1.le, hx.2.le⟩

end Work.FTS.EllSol.Flat
