import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The geometry of the `dℓ`-small box on the good set: shortest side and the
distance to the `ℓ(1/2−ε)` ball

This module proves `Work.BoseB1Cube.shortSideBetaGeom`, the geometric input
for the "`β`-short-side" cube argument: for `u` on the good set
`G = goodSet ℓ d μ` and `x ∈ B(u) = dlBox ℓ d u` with `‖x‖ ≤ ℓ(1/2 − ε)`
(`0 ≤ ε ≤ 1/2`), the coordinate half-sides
`shortSide ℓ d u j = min (ℓd) (½ℓ(1+d) − |((ℓd)•u)_j|)`
of the `u`-indexed box satisfy

* `μ^{-1/3} ≤ shortSide ℓ d u j ≤ ℓd` (the good-set reading, FS `thm:smallbox`),
* the excess of the centre coordinate over the small half-side,
  `e_j := max 0 (|((ℓd)•u)_j| − ℓd/2)`, is `≥ 0` and, on the branch
  `shortSide ℓ d u j < ℓd`, satisfies the exact identity
  `e_j = ℓ/2 − shortSide ℓ d u j`,
* `∑_j e_j² ≤ ℓ²(1/2 − ε)²`.

The mathematical content of the last item is the coordinatewise bound
`e_j ≤ |x_j|`: since `x ∈ B(u)` forces `|x_j − ((ℓd)•u)_j| ≤ ℓd/2` and
`x ∈ acube ℓ`, the excess of the centre coordinate over the half-side can only
be paid by the coordinate of the point `x` itself, and then
`∑_j e_j² ≤ ∑_j x_j² = ‖x‖² ≤ (ℓ(1/2−ε))²`.
-/

namespace Work.BoseB1Cube

open MeasureTheory

/-- Coordinate form of `dlBox`-membership: for `x ∈ B(u)` the `j`-coordinate of
`x` lies within `ℓd/2` of the `j`-coordinate of the small-box centre
`(ℓd)•u`. -/
lemma abs_coord_sub_le_of_mem_dlBox {ℓ d : ℝ} {u x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.BoseGases.dlBox ℓ d u) (j : Fin 3) :
    |x.ofLp j - ((ℓ * d) • u).ofLp j| ≤ ℓ * d / 2 := by
  have h3 := (Submission.BoseGases.mem_acube_iff (ℓ * d) (x - (ℓ * d) • u)).mp
    ((Submission.BoseGases.mem_dlBox_iff ℓ d u x).mp hx).2 j
  rw [Set.mem_Icc] at h3
  obtain ⟨hl, hr⟩ := h3
  rw [abs_le]; constructor <;> · simp at hl hr ⊢; linarith

/-- The excess `max 0 (|((ℓd)•u)_j| − ℓd/2)` of the `j`-th half-side is
dominated by the `j`-th coordinate of any `x ∈ B(u)`. -/
lemma max_sub_le_abs_coord {ℓ d : ℝ} {u x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.BoseGases.dlBox ℓ d u) (j : Fin 3) :
    max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2) ≤ |x.ofLp j| := by
  refine max_le (abs_nonneg _) ?_
  have habs := abs_coord_sub_le_of_mem_dlBox hx j
  have h1 : |((ℓ * d) • u).ofLp j| - |x.ofLp j - ((ℓ * d) • u).ofLp j| ≤ |x.ofLp j| := by
    have h := abs_sub_abs_le_abs_sub (((ℓ * d) • u).ofLp j) (((ℓ * d) • u).ofLp j - x.ofLp j)
    have he : ((ℓ * d) • u).ofLp j - (((ℓ * d) • u).ofLp j - x.ofLp j) = x.ofLp j := by ring
    rw [he] at h
    rw [abs_sub_comm] at h
    linarith
  linarith

/-- `shortSide` is at most the (nominal) small-box side `ℓd`. -/
lemma shortSide_le (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    Work.SmallBoxSliding.shortSide ℓ d u j ≤ ℓ * d := min_le_left _ _

/-- On the branch `shortSide ℓ d u j < ℓd` the `min` in the definition of
`shortSide` is realised by its second argument, so that
`max 0 (|((ℓd)•u)_j| − ℓd/2) = ℓ/2 − shortSide ℓ d u j`.  The hypothesis
`d ≤ 1/2` is what guarantees `|((ℓd)•u)_j| ≥ ℓd/2` on this branch. -/
lemma max_eq_half_sub_shortSide {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd2 : d ≤ 1 / 2)
    {u : EuclideanSpace ℝ (Fin 3)} (j : Fin 3)
    (h : Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d) :
    max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)
      = ℓ / 2 - Work.SmallBoxSliding.shortSide ℓ d u j := by
  set a : ℝ := ((ℓ * d) • u).ofLp j with ha
  have hmins : Work.SmallBoxSliding.shortSide ℓ d u j = (1 / 2) * ℓ * (1 + d) - |a| := by
    rw [Work.SmallBoxSliding.shortSide] at h ⊢
    rcases min_lt_iff.mp h with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact min_eq_right (le_of_lt h')
  have hpos : 0 < |a| - ℓ * d / 2 := by
    have h2 : ℓ * (1 - d) / 2 < |a| := by
      have := h; rw [hmins] at this; linarith
    have h3 : ℓ * d / 2 ≤ ℓ * (1 - d) / 2 := by nlinarith
    linarith
  rw [max_eq_right (le_of_lt hpos), hmins]
  ring

/-- The Pythagorean bound for the `shortSide` excesses: for any `x ∈ B(u)`,
`∑_j (max 0 (|((ℓd)•u)_j| − ℓd/2))² ≤ ‖x‖²`. -/
lemma sum_sq_max_le_normSq {ℓ d : ℝ} {u x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.BoseGases.dlBox ℓ d u) :
    (∑ j : Fin 3, (max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)) ^ 2) ≤ ‖x‖ ^ 2 := by
  have hsum : (∑ j : Fin 3, (max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)) ^ 2)
      ≤ ∑ j : Fin 3, (x.ofLp j) ^ 2 := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hAA := mul_self_le_mul_self (le_max_left (0 : ℝ) _) (max_sub_le_abs_coord hx j)
    simpa [pow_two] using hAA
  have hnorm : (∑ j : Fin 3, (x.ofLp j) ^ 2) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [← hnorm]
  exact hsum

theorem shortSideBetaGeom {ℓ d μ ε : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hd2 : d ≤ 1 / 2) (hμ : 0 < μ) (hreg : μ ^ (-(1 / 3 : ℝ)) ≤ ℓ * d)
    (hε0 : 0 ≤ ε) (hεh : ε ≤ 1 / 2) {u x : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet ℓ d μ)
    (hx : x ∈ Submission.BoseGases.dlBox ℓ d u) (hxnorm : ‖x‖ ≤ ℓ * (1 / 2 - ε)) :
    (∀ j : Fin 3, μ ^ (-(1 / 3 : ℝ)) ≤ Work.SmallBoxSliding.shortSide ℓ d u j) ∧
    (∀ j : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u j ≤ ℓ * d) ∧
    (∀ j : Fin 3, 0 ≤ max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)) ∧
    (∀ j : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d →
        max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2) = ℓ / 2 - Work.SmallBoxSliding.shortSide ℓ d u j) ∧
    (∑ j : Fin 3, (max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)) ^ 2 ≤ ℓ ^ 2 * (1 / 2 - ε) ^ 2) := by
  have hreg' : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d := by
    rw [show (-1 : ℝ) / 3 = -(1 / 3 : ℝ) by norm_num]; exact hreg
  have hside : ∀ j : Fin 3, μ ^ (-(1 / 3 : ℝ)) ≤ Work.SmallBoxSliding.shortSide ℓ d u j := by
    intro j
    have h := Work.SmallBoxSliding.goodSet_shortSide hreg' hu j
    rwa [show (-1 : ℝ) / 3 = -(1 / 3 : ℝ) by norm_num] at h
  refine ⟨hside, fun j => shortSide_le ℓ d u j, fun j => le_max_left _ _,
    fun j => max_eq_half_sub_shortSide hℓ hd2 j, ?_⟩
  calc (∑ j : Fin 3, (max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2)) ^ 2)
      ≤ ‖x‖ ^ 2 := sum_sq_max_le_normSq hx
    _ ≤ (ℓ * (1 / 2 - ε)) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxnorm 2
    _ = ℓ ^ 2 * (1 / 2 - ε) ^ 2 := by ring

end Work.BoseB1Cube
