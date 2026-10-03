import Mathlib
import Submission.Work.Param.CriticalKit

namespace Work.Param.CriticalKit

open Work.Param Filter Topology
open scoped Topology

/-- **Values of a local Koenigs solution lie in the basin of `0`.**  If `‖l‖ < 1` and
`ψ` is a normalized local solution of `Q l (ψ w) = ψ (l * w)` on `Metric.ball 0 r`
(`Good l r ψ`), then the `Q l`-orbit of `ψ w` converges to `0` for every `w` in that ball:
indeed `(Q l)^[n] (ψ w) = ψ (l ^ n * w) → ψ 0 = 0`. -/
theorem good_mem_basin (l : ℂ) (hl : ‖l‖ < 1) {r : ℝ} {ψ : ℂ → ℂ} (h : Good l r ψ) :
    ∀ w ∈ Metric.ball 0 r, Basin l (ψ w) := by
  obtain ⟨hr, hdiff, h0, hderiv, hKo⟩ := h
  intro w hw
  -- The disc is invariant under multiplication by `l` (as `‖l‖ < 1`).
  have hmem : ∀ u ∈ Metric.ball 0 r, l * u ∈ Metric.ball 0 r := by
    intro u hu
    have hu' : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_left] using hu
    rw [Metric.mem_ball, dist_zero_right, norm_mul]
    nlinarith [norm_nonneg u, hl, hu']
  -- The orbit relation `(Q l)^[n] (ψ u) = ψ (l ^ n * u)`, by induction on `n`.
  have hiter : ∀ n : ℕ, ∀ u ∈ Metric.ball 0 r, (Q l)^[n] (ψ u) = ψ (l ^ n * u) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ n ih =>
      intro u hu
      rw [Function.iterate_succ_apply, hKo u hu, ih (l * u) (hmem u hu)]
      congr 1
      rw [pow_succ]; ring
  -- `ψ` is continuous at `0` (it is holomorphic on a neighbourhood of `0`).
  have hcont : ContinuousAt ψ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  -- `l ^ n * w → 0`, hence `ψ (l ^ n * w) → ψ 0 = 0`.
  have hp : Tendsto (fun n : ℕ => l ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hl
  have hpw : Tendsto (fun n : ℕ => l ^ n * w) atTop (nhds 0) := by
    simpa using hp.mul_const w
  have htend : Tendsto (fun n : ℕ => ψ (l ^ n * w)) atTop (nhds 0) := by
    have hc := hcont.tendsto.comp hpw
    simpa [Function.comp_def, h0] using hc
  rw [Basin]
  exact htend.congr' (Eventually.of_forall fun n => (hiter n w hw).symm)

end Work.Param.CriticalKit
