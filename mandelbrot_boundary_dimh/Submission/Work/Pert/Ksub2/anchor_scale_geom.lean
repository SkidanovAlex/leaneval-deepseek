import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.Setup

/-!
# `Work.Pert.Ksub2.anchor_scale_geom`

The elementary geometric fact behind the "deep strip" reductions of `Ksub_phi_close_v2`: for every
datum `d` with `ξ₀ > 0` there is a scale `R` such that every `M ≥ R` is at least `8`, and the disc
of centre `-M` and radius `M/4` is contained in the repelling sector `QLeft ξ₀`.

The disc `ball (-M) (M/4)` has all its points strictly to the left of `-3M/4` (because the real
part is dominated by the modulus), and the left half plane `{Re w < -ξ₀}` is contained in
`QLeft ξ₀` (`Work.Parab.halfplane_subset_QLeft`).  So it suffices to take `M ≥ 4ξ₀/3 + 1`.
-/

namespace Work.Pert.Ksub2

open Metric Complex

theorem anchor_scale_geom {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      8 ≤ M ∧ Metric.ball ((-M : ℝ) : ℂ) (M / 4) ⊆ MandelDim.QLeft d.ξ₀ := by
  refine ⟨max 8 (4 / 3 * d.ξ₀ + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro M hM
    have h8 : 8 ≤ M := le_trans (le_max_left _ _) hM
    have hMbig : 4 / 3 * d.ξ₀ + 1 ≤ M := le_trans (le_max_right _ _) hM
    refine ⟨h8, ?_⟩
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre : (w - ((-M : ℝ) : ℂ)).re = w.re + M := by simp
    have h2 : |w.re + M| < M / 4 := by
      calc |w.re + M| = |(w - ((-M : ℝ) : ℂ)).re| := by rw [hre]
        _ ≤ ‖w - ((-M : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
        _ < M / 4 := hw
    have h3 : w.re + M < M / 4 := (abs_lt.mp h2).2
    have hξ : 0 < d.ξ₀ := d.ξ₀_pos
    have hgoal : w.re < -d.ξ₀ := by linarith
    exact Work.Parab.halfplane_subset_QLeft d.ξ₀ hgoal

end Work.Pert.Ksub2
