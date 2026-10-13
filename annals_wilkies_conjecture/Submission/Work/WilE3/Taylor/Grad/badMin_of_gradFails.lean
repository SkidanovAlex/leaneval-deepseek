import Mathlib
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin

namespace Work.WilE3.Taylor.Grad

theorem badMin_of_gradFails {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hpq : p < q)
    (hbad : ∀ ρ : ℝ, 0 < ρ → ∃ x : Fin k → ℝ, dist x y < ρ ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p)) :
    ∃ (x u : ℕ → Fin k → ℝ), ∀ n : ℕ,
      dist (x n) y < 1 / (2 * (n + 1)) ∧ 0 < Φ (x n) ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ (x n) l) ^ 2) ^ q < (Φ (x n)) ^ (2 * p) ∧
      dist (u n) y ≤ 2 * dist (x n) y ∧ 0 < Φ (u n) ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ (u n) l) ^ 2) ^ q < (Φ (u n)) ^ (2 * p) ∧
      (∀ z : Fin k → ℝ, Φ z = Φ (u n) → dist z y ≤ 2 * dist (x n) y →
        (∑ l, (Work.WilE3.Taylor.grad Φ (u n) l) ^ 2) ≤
          (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2)) := by
  classical
  -- `Φ` and the squared gradient norm `G` are continuous (they are analytic).
  have hΦcont : Continuous Φ := continuous_iff_continuousAt.mpr fun z => (hΦ z).continuousAt
  have hGcont : Continuous fun z : Fin k → ℝ => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2 := by
    refine continuous_finsetSum _ fun l _ => ?_
    exact (continuous_iff_continuousAt.mpr fun z => (analyticAt_grad_comp hΦ l z).continuousAt).pow 2
  -- The sequence `x n` of "bad" points, with `dist (x n) y < 1 / (2 * (n + 1))`.
  choose x hx using fun n : ℕ => hbad (1 / (2 * (n + 1))) (by positivity)
  -- For each `n`, the squared gradient norm `G` attains its minimum on the level set of `Φ`
  -- through `x n`, intersected with the closed ball of radius `2 * dist (x n) y` around `y`.
  have hmin : ∀ n : ℕ, ∃ u : Fin k → ℝ,
      Φ u = Φ (x n) ∧ dist u y ≤ 2 * dist (x n) y ∧
      ∀ z : Fin k → ℝ, Φ z = Φ (x n) → dist z y ≤ 2 * dist (x n) y →
        (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) ≤
          (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) := by
    intro n
    have hcpt : IsCompact ({z : Fin k → ℝ | Φ z = Φ (x n)}
        ∩ Metric.closedBall y (2 * dist (x n) y)) :=
      (isCompact_closedBall y (2 * dist (x n) y)).inter_left
        (isClosed_eq hΦcont continuous_const)
    have hne : ({z : Fin k → ℝ | Φ z = Φ (x n)}
        ∩ Metric.closedBall y (2 * dist (x n) y)).Nonempty :=
      ⟨x n, rfl, by
        rw [Metric.mem_closedBall]
        exact le_mul_of_one_le_left dist_nonneg (by norm_num)⟩
    obtain ⟨u, huS, hu⟩ := hcpt.exists_isMinOn hne hGcont.continuousOn
    exact ⟨u, huS.1, Metric.mem_closedBall.mp huS.2,
      fun z hz hdz => (isMinOn_iff.mp hu) z ⟨hz, hdz⟩⟩
  refine ⟨x, fun n => Classical.choose (hmin n), fun n => ?_⟩
  obtain ⟨hlev, hdu, hminz⟩ := Classical.choose_spec (hmin n)
  obtain ⟨hxd, hxpos, hxbad⟩ := hx n
  have hdx : dist (x n) y ≤ 2 * dist (x n) y :=
    le_mul_of_one_le_left dist_nonneg (by norm_num)
  -- Minimality of `u n` on the level set, applied at `x n`, bounds `G (u n)` by `G (x n)`.
  have hGu : (∑ l, (Work.WilE3.Taylor.grad Φ (Classical.choose (hmin n)) l) ^ 2)
      ≤ (∑ l, (Work.WilE3.Taylor.grad Φ (x n) l) ^ 2) := hminz (x n) rfl hdx
  have hGnn : (0:ℝ) ≤ ∑ l, (Work.WilE3.Taylor.grad Φ (Classical.choose (hmin n)) l) ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  refine ⟨hxd, hxpos, hxbad, hdu, ?_, ?_, ?_⟩
  · -- `0 < Φ (u n)`, since `Φ (u n) = Φ (x n)`.
    rw [hlev]; exact hxpos
  · -- the bad inequality transfers from `x n` to `u n`, as `Φ (u n) = Φ (x n)` and
    -- `G (u n) ≤ G (x n)`
    have h1 := pow_le_pow_left₀ hGnn hGu q
    have h2 : (Φ (x n)) ^ (2 * p) = (Φ (Classical.choose (hmin n))) ^ (2 * p) := by rw [hlev]
    exact lt_of_le_of_lt h1 (h2 ▸ hxbad)
  · -- minimality of `u n` on its own level set inside the ball
    intro z hz hdz
    exact hminz z (hz.trans hlev) hdz

end Work.WilE3.Taylor.Grad
