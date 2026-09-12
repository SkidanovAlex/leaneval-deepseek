import Mathlib
import Submission.Work.Polygon.DiscreteConvex
import Submission.Work.Lattice.LatticePolygon

/-!
# Reverse convexity along the rank equation (the P2/P3 compatibility inequality)

For a discrete-convex `c : ℕ → ℝ` on `{0, …, d}` and integers
`m ≤ k ≤ ℓ ≤ n ≤ d` satisfying the **rank equation** `m + n = k + ℓ` (which is the
rank identity `dim V + dim W = dim (V ⊓ W) + dim (V ⊔ W)` for subgroups of a lattice,
with `m = dim(V⊓W)`, `k = dim V`, `ℓ = dim W`, `n = dim(V⊔W)`), the convexity of `c`
forces the **reverse** inequality

    `c m + c n ≥ c k + c ℓ`.

This is the convexity half of the "compatibility of realisers" analysis of P2-general:
combined with the log-covol submodularity (`AlignedBases.logCovol_submodularity_saturated`,
which gives `c m + c n ≤ c k + c ℓ` when `k`- and `ℓ`-rank subgroups realise the polygon
values at their ranks), it pins `c` to be *affine* on the extremal blocks, forcing the
meet/join ranks to saturate the interval — the mechanism the HN-flag nesting uses
(together with the strict `+2` slack of the quadratic term, Lemma 3 / L49).

The proof is the standard "increasing rearrangement" argument in terms of slopes: write
`c k − c m = Σ_{i < s} dslope (m+i)` and `c n − c ℓ = Σ_{i < s} dslope (ℓ+i)` with
`s := k − m = n − ℓ` (the rank equation), and compare the two sums pointwise by slope
monotonicity (`dslope (m+i) ≤ dslope (ℓ+i)`).

All declarations are Mathlib + `Submission.Work.Polygon.DiscreteConvex`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.Polygon

open Submission.GraysonData
open Submission.LatticePolygon

/-- Shifted telescoping: `c (a + s) = c a + Σ_{i < s} dslope c (a + i)`. -/
lemma telescope_shift (c : ℕ → ℝ) (a s : ℕ) :
    (∑ i ∈ Finset.range s, dslope c (a + i)) = c (a + s) - c a := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [dslope]
      have : a + (s + 1) = (a + s) + 1 := by omega
      rw [this]
      ring

/-- **Slope monotonicity on the full slope range** (`dslope` is non-decreasing on
`{0, …, d−1}` for a discrete-convex function), with the sharper bound `j + 1 ≤ d`. -/
lemma dslope_mono {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 1 ≤ d) : dslope c i ≤ dslope c j := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  · have hstep : dslope c (j - 1) ≤ dslope c j := by
      have h := hcvx (j - 1) (by omega)
      have : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hjpos
      simpa [this] using h
    rcases lt_or_eq_of_le hij with hij' | hij''
    · have hprev : dslope c i ≤ dslope c (j - 1) := by
        apply slope_le_of_le hcvx (i := i) (j := j - 1) (by omega) (by omega)
      exact le_trans hprev hstep
    · subst hij''
      rfl

/-- **Reverse convexity along the rank equation**: for discrete-convex `c` on `{0,…,d}`
and `m ≤ k ≤ ℓ ≤ n ≤ d` with `m + n = k + ℓ`, one has `c m + c n ≥ c k + c ℓ`. -/
lemma convex_rank_equation {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {m k ℓ n : ℕ}
    (hmk : m ≤ k) (hkℓ : k ≤ ℓ) (_hℓn : ℓ ≤ n) (hn : n ≤ d) (heq : m + n = k + ℓ) :
    c m + c n ≥ c k + c ℓ := by
  classical
  have hs_eq : k - m = n - ℓ := by omega
  set s : ℕ := k - m with hsdef
  have hms : m + s = k := by omega
  have hℓs : ℓ + s = n := by omega
  have hshiftm : c k - c m = ∑ i ∈ Finset.range s, dslope c (m + i) := by
    have h := telescope_shift c m s
    rw [hms] at h
    linarith
  have hshiftℓ : c n - c ℓ = ∑ i ∈ Finset.range s, dslope c (ℓ + i) := by
    have h := telescope_shift c ℓ s
    rw [hℓs] at h
    linarith
  have hsum : (∑ i ∈ Finset.range s, dslope c (m + i)) ≤
      (∑ i ∈ Finset.range s, dslope c (ℓ + i)) := by
    apply Finset.sum_le_sum
    intro i hi
    have his : i < s := Finset.mem_range.mp hi
    apply dslope_mono hcvx (i := m + i) (j := ℓ + i) (by omega) (by omega)
  linarith

/-! ## The Grayson polygon along rank equations -/

/-- The Grayson polygon of `Λ` satisfies the reverse convexity along the rank equation
`m + n = k + ℓ` (with `m ≤ k ≤ ℓ ≤ n ≤ d`): `polygon Λ m + polygon Λ n ≥
polygon Λ k + polygon Λ ℓ`. -/
theorem polygon_rank_equation {d : ℕ} (Λ : Submodule ℤ (E d))
    (hΛfin : Module.finrank ℤ Λ = d) {m k ℓ n : ℕ}
    (hmk : m ≤ k) (hkℓ : k ≤ ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ d) (heq : m + n = k + ℓ) :
    polygon Λ m + polygon Λ n ≥
      polygon Λ k + polygon Λ ℓ := by
  have hpoly : polygon Λ = fun i => largestConvexMinorant d (rankData Λ) i := by
    funext i
    simp only [polygon]
    rw [hΛfin]
  have hcvx : DiscreteConvexOn (polygon Λ) d := by
    rw [hpoly]
    exact largestConvexMinorant_convex d (rankData Λ)
  exact convex_rank_equation hcvx hmk hkℓ hℓn hn heq

end Submission.Polygon
