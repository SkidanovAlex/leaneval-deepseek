import Mathlib
import Submission.Work.Param.CriticalKit

namespace Work.Param.CriticalKit

/-- The basin of attraction of `0` for `Q l x = l * x + x ^ 2` is bounded: there is `M` with
`‖y‖ ≤ M` for every `y` whose orbit converges to `0`.  (Take `M = ‖l‖ + 1`: if `‖y‖ ≥ ‖l‖ + 1`
then `‖Q l y‖ ≥ ‖y‖ (‖y‖ - ‖l‖) ≥ ‖y‖`, so all iterates keep norm `≥ ‖y‖ > 0` and the orbit
cannot converge to `0`.) -/
theorem basin_bounded (l : ℂ) : ∃ M : ℝ, ∀ y : ℂ, Basin l y → ‖y‖ ≤ M := by
  refine ⟨‖l‖ + 1, fun y hy => ?_⟩
  by_contra hbad
  rw [not_le] at hbad
  -- hbad : ‖l‖ + 1 < ‖y‖
  -- Reverse triangle: for `‖x‖ ≥ ‖l‖ + 1` the map `Q l` does not decrease the norm.
  have hkey : ∀ x : ℂ, ‖l‖ + 1 ≤ ‖x‖ → ‖x‖ ≤ ‖Q l x‖ := by
    intro x hx
    have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have htri : ‖x ^ 2‖ ≤ ‖Q l x‖ + ‖l * x‖ := by
      have h := norm_add_le (Q l x) (-(l * x))
      rw [norm_neg] at h
      have he : Q l x + -(l * x) = x ^ 2 := by simp only [Q]; ring
      rwa [he] at h
    rw [norm_pow, norm_mul] at htri
    have h4 : ‖x‖ * (‖x‖ - ‖l‖) ≤ ‖Q l x‖ := by nlinarith [htri]
    have h5 : ‖x‖ ≤ ‖x‖ * (‖x‖ - ‖l‖) := by
      have hd : 1 ≤ ‖x‖ - ‖l‖ := by linarith
      calc ‖x‖ = ‖x‖ * 1 := by ring
        _ ≤ ‖x‖ * (‖x‖ - ‖l‖) := mul_le_mul_of_nonneg_left hd hxnn
    linarith
  -- Hence every iterate keeps norm `≥ ‖y‖`.
  have hgrow : ∀ n : ℕ, ‖y‖ ≤ ‖(Q l)^[n] y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (hkey _ (le_trans (le_of_lt hbad) ih))
  have hy0 : (0 : ℝ) < ‖y‖ := by linarith [norm_nonneg l]
  obtain ⟨n, hn⟩ := (hy.eventually (Metric.ball_mem_nhds 0 hy0)).exists
  have hn' : ‖(Q l)^[n] y‖ < ‖y‖ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hn
  linarith [hgrow n]

end Work.Param.CriticalKit
