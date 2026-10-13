/-
  WilG1 / Cell / Stair / Basic.

  The "staircase path" from `y` to `x` in `ℝⁿ`:  `stair x y k` agrees with `x` in the
  coordinates `< k` and with `y` in the coordinates `≥ k`.  Consecutive vertices differ in a
  single coordinate, which is what makes it possible to write `h x - h y` as a sum of `n`
  one-dimensional differences, each of which can be estimated along a *fibre* of `h`.

  This file contains only the (elementary, analysis-free) combinatorics of the staircase,
  together with the norm estimates that locate the staircase inside the sup-metric ball
  around `y`.
-/
import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilG1.Cell

/-- The `k`-th vertex of the staircase from `y` to `x`: coordinates `< k` equal `x`, the
remaining coordinates equal `y`. -/
def stair {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < k then x i else y i

/-- The point of the segment in direction `k` from `stair x y k` to `stair x y (k+1)`: the
coordinate `k` is set to `t`, all other coordinates are those of `stair x y k`. -/
def stairSeg {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update (stair x y k) k t

@[simp] theorem stair_apply {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    stair x y k i = if (i : ℕ) < k then x i else y i := rfl

@[simp] theorem stairSeg_apply {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) (t : ℝ) (i : Fin n) :
    stairSeg x y k t i = if i = k then t else stair x y (k : ℕ) i := by
  rw [stairSeg, Function.update_apply]

theorem stair_zero {n : ℕ} (x y : Fin n → ℝ) : stair x y 0 = y := by
  funext i
  simp

theorem stair_self {n : ℕ} (x y : Fin n → ℝ) : stair x y n = x := by
  funext i
  rw [stair_apply, if_pos i.isLt]

theorem stair_sub_apply {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    (stair x y k - y) i = if (i : ℕ) < k then x i - y i else 0 := by
  rw [Pi.sub_apply, stair_apply]
  split <;> simp

theorem stair_sub_le {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) : ‖stair x y k - y‖ ≤ ‖x - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [stair_sub_apply]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h]
    simpa using norm_le_pi_norm (x - y) i
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

theorem stair_succ {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) :
    stair x y ((k : ℕ) + 1) = Function.update (stair x y k) k (x k) := by
  funext i
  rw [Function.update_apply]
  by_cases hik : i = k
  · subst hik
    simp [stair_apply]
  · rw [if_neg hik]
    have hiff : ((i : ℕ) < (k : ℕ) + 1) ↔ ((i : ℕ) < (k : ℕ)) := by
      constructor
      · intro hlt
        by_contra hcon
        exact hik (Fin.ext (by omega))
      · exact Nat.lt_succ_of_lt
    exact if_congr hiff rfl rfl

theorem stair_succ_of_eq {n : ℕ} {x y : Fin n → ℝ} {k : Fin n} (hk : x k = y k) :
    stair x y ((k : ℕ) + 1) = stair x y k := by
  rw [stair_succ, hk]
  rw [show y k = stair x y (k : ℕ) k from by simp]
  exact Function.update_eq_self k (stair x y (k : ℕ))

theorem stairSeg_sub_le {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    ‖stairSeg x y k t - y‖ ≤ max ‖x - y‖ |t - y k| := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  rw [Pi.sub_apply, stairSeg_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact le_max_right _ _
  · rw [if_neg hik]
    have h1 : ‖stair x y (k : ℕ) i - y i‖ ≤ ‖x - y‖ := by
      have := (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).1 (stair_sub_le x y (k : ℕ)) i
      simpa [Pi.sub_apply] using this
    exact h1.trans (le_max_left _ _)

theorem stairSeg_sub_le' {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) {t : ℝ}
    (ht : t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k))) :
    ‖stairSeg x y k t - y‖ ≤ ‖x - y‖ := by
  refine (stairSeg_sub_le x y k t).trans ?_
  refine max_le ?_ ?_
  · exact le_rfl
  · have h2 : |t - y k| ≤ |x k - y k| := by
      rcases le_total (x k) (y k) with h | h
      · rw [min_eq_left h, max_eq_right h] at ht
        have : t ≤ y k := ht.2
        rw [abs_of_nonpos (sub_nonpos.2 this), abs_of_nonpos (sub_nonpos.2 h), neg_sub]
        linarith [ht.1]
      · rw [min_eq_right h, max_eq_left h] at ht
        have : y k ≤ t := ht.1
        rw [abs_of_nonneg (sub_nonneg.2 this), abs_of_nonneg (sub_nonneg.2 h)]
        linarith [ht.2]
    calc |t - y k| ≤ |x k - y k| := h2
      _ = ‖(x - y) k‖ := by rw [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) k

theorem fibreMap_stairSeg {n : ℕ} (h : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) (k : Fin n) (c : ℝ) :
    fibreMap h k (stairSeg x y k c) = fibreMap h k (stair x y k) := by
  funext t
  show h (Function.update (Function.update (stair x y (k : ℕ)) k c) k t) =
    h (Function.update (stair x y (k : ℕ)) k t)
  rw [Function.update_idem c t (stair x y (k : ℕ))]

theorem stairSeg_self {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) :
    stairSeg x y k (y k) = stair x y (k : ℕ) := by
  rw [stairSeg, show y k = stair x y (k : ℕ) k from by simp]
  exact Function.update_eq_self k (stair x y (k : ℕ))

theorem stairSeg_succ {n : ℕ} (x y : Fin n → ℝ) (k : Fin n) :
    stairSeg x y k (x k) = stair x y ((k : ℕ) + 1) := by
  rw [stair_succ]
  rfl

theorem sum_stair_sub {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    ∑ k : Fin n, (f (stair x y ((k : ℕ) + 1)) - f (stair x y (k : ℕ))) = f x - f y := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (stair x y (k + 1)) - f (stair x y k)) n]
  rw [Finset.sum_range_sub (fun k => f (stair x y k)) n, stair_zero, stair_self]

theorem sum_stair_sub' {n : ℕ} (h : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    ∑ k : Fin n, (h (stairSeg x y k (x k)) - h (stairSeg x y k (y k))) = h x - h y := by
  have h1 : ∀ k : Fin n, h (stairSeg x y k (x k)) = h (stair x y ((k : ℕ) + 1)) := by
    intro k; rw [stairSeg_succ]
  have h2 : ∀ k : Fin n, h (stairSeg x y k (y k)) = h (stair x y (k : ℕ)) := by
    intro k; rw [stairSeg_self]
  simp only [h1, h2]
  exact sum_stair_sub h x y

end Work.WilG1.Cell
