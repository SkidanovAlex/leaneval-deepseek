import Mathlib
import Submission.Work.Pert.Count.card_le_of_mono_walk
import Submission.Work.Pert.Count.walk_telescope_le
import Submission.Work.Pert.Count.exists_int_dist_le_of_infDist_le
import Submission.Work.Pert.LCH.infDist_int_eq_round

namespace Work.Pert

/-! A monotone real walk visits the neighbourhoods of the lattice proportionally to their size:
for `m : ℕ → ℝ` on `{0,…,n}` with steps in `[c₀, c₁]` and `0 < s ≤ 1/2`, at most
`(n c₁ + 2)(2 s / c₀ + 1)` indices `j ≤ n` have `dist (m j) ℤ ≤ s`.
Proof route: group the indices by the nearest integer `k = ⌊m j + 1/2⌋`; since `m` increases with
step `≥ c₀`, all values lie in `[m 0, m n]`, which meets at most `m n - m 0 + 2` integer cells
(the integers in `[m0 - s, mn + s]`, using `2s ≤ 1`), and each cell contains at most
`2 s / c₀ + 1` of the indices (apply `card_le_of_gap` with `a = k - s`, `b = k + s`; note that a
counted index may lie in two cells, which only helps).
Already available (public, in this workspace): `Work.Pert.LCH.card_le_of_gap` and
`Work.Pert.LCH.infDist_int_eq_round` (files under `Submission/Work/Pert/LCH/`). -/

theorem count_walk_level {m : ℕ → ℝ} {c₀ c₁ s : ℝ} {n : ℕ}
    (hc0 : 0 < c₀) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hstep : ∀ j < n, c₀ ≤ m (j + 1) - m j ∧ m (j + 1) - m j ≤ c₁) :
    (((Finset.range (n + 1)).filter
        (fun j => Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ s)).card : ℝ)
      ≤ ((n : ℝ) * c₁ + 2) * (2 * s / c₀ + 1) := by
  classical
  -- 1. The steps give monotonicity with gap `c₀`.
  have hmono : ∀ j < n, m j + c₀ ≤ m (j + 1) := fun j hj => by
    have h := (hstep j hj).1
    linarith
  -- 2. A point within distance `s` of the lattice has `round` as an explicit witness.
  have hp : ∀ j ≤ n, Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ s →
      ∃ k : ℤ, dist (m j) (k : ℝ) ≤ s := fun j _ hj =>
    Work.Pert.Count.exists_int_dist_le_of_infDist_le hj
  -- 3. The general counting lemma for a monotone walk, with the window `[m 0, m n]`.
  have hkey := Work.Pert.Count.card_le_of_mono_walk (t := m) (n := n) (s := s) (δ := c₀)
    (p := fun j => Metric.infDist (m j) (Set.range (fun k : ℤ => (k : ℝ))) ≤ s)
    hc0 (le_of_lt hs) hmono hp
  refine le_trans hkey ?_
  -- 4. `m n - m 0 ≤ n c₁` and `2 s ≤ 1` turn the window into `n c₁ + 2`.
  have hmn := Work.Pert.Count.walk_telescope_le (m := m) (c₁ := c₁) (n := n)
    (fun j hj => (hstep j hj).2)
  have hb : (0 : ℝ) ≤ 2 * s / c₀ + 1 := by
    have h : (0 : ℝ) ≤ 2 * s / c₀ := div_nonneg (by linarith) hc0.le
    linarith
  have h1 : (m n - m 0) + 2 * s + 1 ≤ (n : ℝ) * c₁ + 2 := by linarith
  exact mul_le_mul_of_nonneg_right h1 hb

end Work.Pert
