import Submission.FUP.TwoConstants
import Submission.Commons.Analysis.Complex.riesz_cartan_disk_nonzero
import Submission.Commons.Analysis.Complex.cartan_polydisk_measure

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The Cartan ingredient for `cartes_polydisk_measure`, and the diskwise constant

`Commons.Analysis.Complex.cartan_polydisk_measure` takes as a hypothesis (`h1`) the
one-dimensional statement: for `g` holomorphic on a neighbourhood of the closed unit disk and
bounded by `M` there (`M ≥ 1`), with a non-zero witness point `z₀` of modulus at most `1-3δ`
where `log‖g z₀‖ ≥ m'`, the measure of the set
`{x : |x| ≤ 1-2δ ∧ log‖g (x:ℂ)‖ < m' - (log M - m')K}` is at most `ofReal (10H)`.

Here we obtain `h1` from the commons theorem
`Commons.Analysis.Complex.riesz_cartan_disk_nonzero` (which produces disks of total radius `≤ 5H`
outside which the lower bound holds) together with
`Submission.FUP.volume_bad_trace_le` (the real trace of such a union of disks has measure
`≤ 2·(5H) = 10H`).
-/

namespace Submission.FUP

/-- **The `h1` hypothesis of `Commons.Analysis.Complex.cartan_polydisk_measure`**, obtained from
`riesz_cartan_disk_nonzero`. -/
lemma cartanDisk_bad_measure {δ H M : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H)
    (hH1 : H ≤ 1) (hM1 : 1 ≤ M) :
    ∀ (g : ℂ → ℂ), AnalyticOnNhd ℂ g (Metric.closedBall 0 1) → ∀ (m' : ℝ),
      (∃ z : ℂ, ‖z‖ ≤ 1 - 3 * δ ∧ g z ≠ 0 ∧ m' ≤ Real.log ‖g z‖) →
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z‖ ≤ M) →
      MeasureTheory.volume {x : ℝ | |x| ≤ 1 - 2 * δ ∧ Real.log ‖g (x : ℂ)‖ <
          m' - (Real.log M - m') *
            (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))}
        ≤ ENNReal.ofReal (10 * H) := by
  intro g hg m' hm hM
  obtain ⟨s, r, hpos, hsum, hout⟩ :=
    Commons.Analysis.Complex.riesz_cartan_disk_nonzero g hg hδ0 hδ3 hH0 hH1 hm hM1 hM
  set L : ℝ := 2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H)
    with hL
  have hsub : {x : ℝ | |x| ≤ 1 - 2 * δ ∧ Real.log ‖g (x : ℂ)‖ < m' - (Real.log M - m') * L}
      ⊆ {x : ℝ | ∃ w ∈ s, ‖(x : ℂ) - w‖ < r w} := by
    rintro x ⟨hx, hxl⟩
    by_contra hc
    have hc' : ∀ w ∈ s, r w ≤ ‖(x : ℂ) - w‖ := by
      intro w hw
      by_contra h
      exact hc ⟨w, hw, lt_of_not_ge h⟩
    have hx' : ‖((x : ℂ))‖ ≤ 1 - 2 * δ := by rwa [Complex.norm_real, Real.norm_eq_abs]
    have hout' := hout (x : ℂ) hx' hc'
    rw [hL] at hxl
    linarith
  calc MeasureTheory.volume {x : ℝ | |x| ≤ 1 - 2 * δ ∧
        Real.log ‖g (x : ℂ)‖ < m' - (Real.log M - m') * L}
      ≤ MeasureTheory.volume {x : ℝ | ∃ w ∈ s, ‖(x : ℂ) - w‖ < r w} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * ∑ z ∈ s, r z) := volume_bad_trace_le s r hpos
    _ ≤ ENNReal.ofReal (10 * H) := ENNReal.ofReal_le_ofReal (by linarith)

end Submission.FUP
