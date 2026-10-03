import Mathlib
import Submission.Work.L61.Basic

namespace Work.L61.CovAux

theorem eventually_eq_zero_of_int_valued {X : Type*} [TopologicalSpace X] {u : X → ℂ} {x : X}
    (hu : ContinuousAt u x) (hint : ∀ y, ∃ n : ℤ, u y = (n : ℂ)) (hx : u x = 0) :
    Filter.Eventually (fun y => u y = 0) (nhds x) := by
  have hball : ∀ᶠ y in nhds x, u y ∈ Metric.ball (u x) 1 :=
    hu.eventually (Metric.ball_mem_nhds (u x) one_pos)
  filter_upwards [hball] with y hy
  obtain ⟨n, hn⟩ := hint y
  rw [Metric.mem_ball, dist_eq_norm, hx, sub_zero] at hy
  have hn0 : n = 0 := by
    have h1 : |(n : ℝ)| < 1 := by
      rw [← Complex.norm_intCast]
      rwa [hn] at hy
    have h2 : ((|n| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
    have h3 : (|n| : ℤ) < 1 := by exact_mod_cast h2
    have h4 : |n| ≤ 0 := by omega
    have h5 : |n| = 0 := le_antisymm h4 (abs_nonneg n)
    exact abs_eq_zero.mp h5
  rw [hn, hn0]; simp

end Work.L61.CovAux
