import Mathlib

/-!
# Propagation of smallness: geometric scaffolding

This file sets up the geometric notions used in the proof of
`Work.TMComp.MAnalytic.propagate`: propagation of smallness for bounded holomorphic
functions on a connected open set.

The quantitative input is the (Hadamard) three-lines inequality, packaged as
`propagate_step`: if `f` is holomorphic on `W ⊇ closedBall a (2R)`, `‖f‖ ≤ 1` on
`closedBall a (2R)` and `‖f‖ ≤ exp(-δ)` on `closedBall a R`, then `‖f‖ ≤ exp(-δ/2)`
on `closedBall a (R * √2)`.  I.e. one step multiplies the "known ball" radius by `√2`
and halves the decay exponent.

Iterating such steps along a curve is encoded by the states `G W r a n` (pairs
`(y, R)` reachable in `≤ n` steps from the initial state `(a, r/2)`), and the
subset `S W r a n ⊆ W` of reachable points.
-/

namespace Work.TMComp.MAnalytic

/-- One propagation step from the state `(y, R)` to the state `(y', R')`: the source ball
`closedBall y (2R)` must lie in `W` (so that holomorphy / the bound `‖f‖ ≤ 1` is available
there), and the target ball `closedBall y' R'` must be contained in `closedBall y (R * √2)`,
which is the region reached by a single three-lines step. -/
def Step (W : Set ℂ) (y : ℂ) (R : ℝ) (y' : ℂ) (R' : ℝ) : Prop :=
  0 < R' ∧ Metric.closedBall y (2 * R) ⊆ W ∧ ‖y' - y‖ + R' ≤ R * Real.sqrt 2

/-- States reachable in at most `n` steps from the initial state `(a, r/2)`.
A state carries a centre and a radius: the ball of that radius around the centre is a
region where a uniform bound is known. -/
def G (W : Set ℂ) (r : ℝ) (a : ℂ) : ℕ → Set (ℂ × ℝ)
  | 0 => {p | p.1 = a ∧ 0 < p.2 ∧ p.2 ≤ r / 2}
  | n + 1 => G W r a n ∪ {p | ∃ q ∈ G W r a n, Step W q.1 q.2 p.1 p.2}

/-- The points of `W` reached in at most `n` steps. -/
def S (W : Set ℂ) (r : ℝ) (a : ℂ) (n : ℕ) : Set ℂ :=
  {z | ∃ R, (z, R) ∈ G W r a n}

theorem G_mono (W : Set ℂ) (r : ℝ) (a : ℂ) (n : ℕ) : G W r a n ⊆ G W r a (n + 1) :=
  Set.subset_union_left

theorem S_mono {W : Set ℂ} {r : ℝ} {a : ℂ} {n : ℕ} : S W r a n ⊆ S W r a (n + 1) := by
  rintro z ⟨R, hR⟩
  exact ⟨R, G_mono W r a n hR⟩

theorem mem_G_pos {W : Set ℂ} {r : ℝ} {a : ℂ} (n : ℕ) :
    ∀ {y : ℂ} {R : ℝ}, (y, R) ∈ G W r a n → 0 < R := by
  induction n with
  | zero => intro y R h; exact h.2.1
  | succ n ih =>
    intro y R h
    rcases h with h | ⟨q, hq, hstep⟩
    · exact ih h
    · exact hstep.1

theorem mem_G_ball {W : Set ℂ} {r : ℝ} {a : ℂ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ W) (n : ℕ) :
    ∀ {y : ℂ} {R : ℝ}, (y, R) ∈ G W r a n → Metric.closedBall y R ⊆ W := by
  induction n with
  | zero =>
    intro y R h
    obtain ⟨hy, -, hle⟩ := h
    subst hy
    refine subset_trans ?_ hball
    intro z hz
    simp only [Metric.mem_closedBall] at hz ⊢
    linarith
  | succ n ih =>
    intro y R h
    rcases h with h | ⟨q, hq, hstep⟩
    · exact ih h
    · obtain ⟨hR', hW', hdist⟩ := hstep
      refine subset_trans ?_ hW'
      intro z hz
      simp only [Metric.mem_closedBall] at hz ⊢
      have h1 : dist z q.1 ≤ dist z y + dist y q.1 := dist_triangle _ _ _
      have h2 : dist y q.1 + R ≤ q.2 * Real.sqrt 2 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hdist
      have hqpos : (0:ℝ) < q.2 := mem_G_pos n hq
      have hsqrt : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_iff]; norm_num
      calc dist z q.1 ≤ dist z y + dist y q.1 := h1
        _ ≤ R + dist y q.1 := by linarith [hz]
        _ ≤ q.2 * Real.sqrt 2 := by linarith [h2]
        _ ≤ q.2 * 2 := by nlinarith [hsqrt, hqpos]
        _ = 2 * q.2 := by ring

end Work.TMComp.MAnalytic
