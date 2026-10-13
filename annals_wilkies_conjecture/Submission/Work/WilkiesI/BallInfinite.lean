import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilkiesI

/-- In a product of copies of `ℝ` indexed by a nonempty finite type, the map
`t ↦ x + t • e_i` (varying one coordinate) is injective on the interval `(0, r)`
and lands in the ball of radius `r`. -/
theorem BallInfinite {μ : ℕ} (hμ : 0 < μ) (x : Fin μ → ℝ) {r : ℝ} (hr : 0 < r) : (Metric.ball x r).Infinite := by
  let i : Fin μ := ⟨0, hμ⟩
  let f : ℝ → (Fin μ → ℝ) := fun t => Function.update x i (x i + t)
  have hinj : Set.InjOn f (Set.Ioo (0 : ℝ) r) := by
    intro a _ b _ hab
    have h1 : x i + a = x i + b := by
      have := congrFun hab i
      simpa [f, Function.update_self] using this
    exact add_left_cancel h1
  have hmaps : Set.MapsTo f (Set.Ioo (0 : ℝ) r) (Metric.ball x r) := by
    intro t ht
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro b
    by_cases hb : b = i
    · rw [hb]
      dsimp only [f]
      rw [Function.update_self, Real.dist_eq]
      have h2 : x i + t - x i = t := by ring
      rw [h2, abs_of_pos ht.1]
      exact ht.2
    · dsimp only [f]
      rw [Function.update_of_ne hb, dist_self]
      exact hr
  exact Set.infinite_of_injOn_mapsTo hinj hmaps (Set.Ioo_infinite hr)

end Work.WilkiesI
