import Mathlib

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- Shifting the index of a range sum by one, when the endpoint values agree:
`∑_{i<Q} g (i+1) = ∑_{i<Q} g i` provided `g Q = g 0`.

Both sides are written as `(∑_{i<Q-1} g (i+1)) + (boundary term)`, and the boundary terms
`g Q` and `g 0` agree, so no cancellation is needed (this matters for `ℝ≥0∞`). -/
lemma sum_range_shift {α : Type*} [AddCommMonoid α] (g : ℕ → α) (Q : ℕ) (h : g Q = g 0) :
    ∑ i ∈ Finset.range Q, g (i + 1) = ∑ i ∈ Finset.range Q, g i := by
  cases Q with
  | zero => simp
  | succ Q' =>
    rw [Finset.sum_range_succ (fun i => g (i + 1)) Q', Finset.sum_range_succ' g Q']
    rw [h]

/-- One step of the invariance of a `Q`-window sum of a `Q`-periodic function. -/
lemma window_sum_succ (F : ℤ → ℝ≥0∞) (Q : ℕ)
    (hF : ∀ v : ℤ, F (v + (Q : ℤ)) = F v) (z : ℤ) :
    ∑ u ∈ Finset.range Q, F (z + 1 + (u : ℤ)) = ∑ u ∈ Finset.range Q, F (z + (u : ℤ)) := by
  have h1 : (∑ i ∈ Finset.range Q, F (z + 1 + (i:ℤ)))
      = ∑ i ∈ Finset.range Q, F (z + (((i+1:ℕ)):ℤ)) :=
    Finset.sum_congr rfl (fun i _ => by congr 1; push_cast; ring)
  rw [h1]
  exact sum_range_shift (fun u : ℕ => F (z + (u : ℤ))) Q (by simpa using hF z)

/-- The `Q`-window sum of a `Q`-periodic function is independent of the base point:
`∑_{u<Q} F (z+u) = ∑_{u<Q} F u`.  Proved by `ℤ`-induction from the one-step invariance. -/
lemma window_sum_const (F : ℤ → ℝ≥0∞) (Q : ℕ)
    (hF : ∀ v : ℤ, F (v + (Q : ℤ)) = F v) (z : ℤ) :
    ∑ u ∈ Finset.range Q, F (z + (u : ℤ)) = ∑ u ∈ Finset.range Q, F (u : ℤ) := by
  refine Int.induction_on z ?_ ?_ ?_
  · simp
  · intro n ih
    rw [window_sum_succ F Q hF (n : ℤ)]
    exact ih
  · intro n ih
    have h := window_sum_succ F Q hF (-(n:ℤ) - 1)
    rw [show -(n:ℤ) - 1 + 1 = -(n:ℤ) by ring] at h
    rw [← h]
    exact ih

/-- **Sums over a complete residue system of a periodic function.**  If `F : ℤ → ℝ≥0∞` is `Q`-periodic
(`F (v + Q) = F v`, `Q > 0`) then the window `y - u`, `u ∈ {0,…,Q-1}`, meets every residue class mod
`Q` exactly once and therefore reproduces the sum over `{0,…,Q-1}`.  Proof: `S₊(y) := Σ_{u<Q}F(y+u)`
and `S₋(y) := Σ_{u<Q}F(y-u)` are both invariant under `y ↦ y+1` (telescoping:
`S₊(y+1) - S₊(y) = F(y+Q) - F(y) = 0`, `S₋(y+1) - S₋(y) = F(y+1) - F(y-Q+1) = 0`), hence constant in
`y`; and `S₋(y) = S₊(y+1)` by the reflection reindexing `u ↦ Q-1-u` together with the periodicity,
so `S₋(y) = S₊(y+1) = S₊(0) = Σ_{u<Q}F(u)`. -/
theorem mstSumResidue (F : ℤ → ℝ≥0∞) (Q : ℕ) (hQpos : 0 < Q)
    (hF : ∀ v : ℤ, F (v + (Q : ℤ)) = F v) (y : ℤ) :
    ∑ u ∈ Finset.range Q, F (y - (u : ℤ)) = ∑ u ∈ Finset.range Q, F (u : ℤ) := by
  -- Reflection `u ↦ Q-1-u` turns the descending window `y-u` into the ascending window based at
  -- `y - Q + 1`, using periodicity at the endpoints.
  have hreflect : (∑ u ∈ Finset.range Q, F (y - (u:ℤ)))
      = ∑ u ∈ Finset.range Q, F ((y - (Q:ℤ) + 1) + (u:ℤ)) := by
    rw [← Finset.sum_range_reflect (fun u => F (y - (u:ℤ))) Q]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ Q - 1 := by
      simp only [Finset.mem_range] at hj
      omega
    congr 1
    rw [Nat.cast_sub hj', Nat.cast_pred hQpos]
    ring
  -- Window sums of a `Q`-periodic function do not depend on the base point.
  rw [hreflect, window_sum_const F Q hF (y - (Q:ℤ) + 1)]

end Work.BourgainPlan.Maximal
