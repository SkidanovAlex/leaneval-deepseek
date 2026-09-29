import Mathlib
import Submission.Work.PureP.basic
import Submission.Work.CPull.defs
import Submission.Work.CPull.germs
import Submission.Work.CPull.hasSum_coeff_B3_yps

/-!
# Area PureP — the pullback germ of `B₃` along an arbitrary lifted map

Generic form of `Submission.Work.CPull.germ_B3` (proved for `φ_C`).  With the odd logarithm `ℓ`
of `1 - Φ` (`Work.PureP.exists_odd_log_phi`), the *even* holomorphic function
`E z = -(1/2) · ℓ z ^ 2` has the same germ as `Σₙ [yⁿ]B₃ · φ (z^2)ⁿ` (this is
`Work.CPull.hasSum_coeff_B3_yps` at `x = Φ z`, using `φ (z^2) = Φ z ^ 2/(Φ z - 1)` and
`ℓ = log (1 - Φ ·)` near `0`), and `Work.CPull.germ_of_even` descends through `z ↦ z ^ 2`.
-/

namespace Work.PureP

open Complex Metric Filter
open scoped Topology
open Submission.CDTPlan

/-- The pullback germ of `B₃` along any `φ` admitting a lift `Φ`, with denominator `1`. -/
theorem germ_B3 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n B3 : ℚ) : ℂ) * φ w ^ n) (N w) := by
  obtain ⟨ℓ, r, hrpos, hrle1, hℓdiff, hℓ0, hℓexp, hℓodd, hℓlog⟩ :=
    exists_odd_log_phi hL.1 (lift_zero hφ0 hL) (lift_ne_one hL) (one_sub_neg hL)
  -- the radius at which `Φ` is small
  have hΦcont : ContinuousAt Φ 0 :=
    hL.1.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hsmall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Φ z‖ < 1 / 2 := by
    have h := hΦcont.eventually (Metric.ball_mem_nhds (Φ 0) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h] with z hz
    rw [lift_zero hφ0 hL] at hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  -- the germ identity for `E z = -(1/2) ℓ z ^ 2`
  have hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n B3 : ℚ) : ℂ) * φ (z ^ 2) ^ n) (-(1 / 2 : ℂ) * ℓ z ^ 2) := by
    filter_upwards [hsmall, Metric.ball_mem_nhds (0 : ℂ) hrpos] with z hzsmall hzr
    have hz1 : ‖z‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hzr
      exact lt_of_lt_of_le hzr hrle1
    have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hlog : ℓ z = Complex.log (1 - Φ z) := hℓlog z hzr
    have hmain := Work.CPull.hasSum_coeff_B3_yps (Φ z) hzsmall
    rw [hlog]
    refine hmain.congr_fun fun n => ?_
    rw [phi_sq_eq hL z hzball]
  exact Work.CPull.germ_of_even (Ψ := φ) (f := B3) (E := fun z => -(1 / 2 : ℂ) * ℓ z ^ 2)
    ((hℓdiff.pow 2).const_mul _)
    (fun z hz => by
      have hneg : -z ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right] at hz ⊢
        simpa using hz
      rw [hℓodd z hz]
      ring)
    hgerm

end Work.PureP
