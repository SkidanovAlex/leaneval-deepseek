/-
  WilG1 / Calc / closure_char.

  The closure criterion used by `Work.WilG1.Calc.closure_mem`:

    `closure X = {x | ∀ r ≠ 0, ∃ y ∈ X, ∑ i (y i - x i)^2 ≤ r ^ 2}`.

  Here `Fin n → ℝ` carries the product (sup) metric, so
  `dist y x ≤ ε ↔ ∀ i, |y i - x i| ≤ ε` (`dist_pi_le_iff`).  The two directions are

  * from the sum of squares to the sup distance: each term is bounded by the whole sum,
    hence `(y i - x i)^2 ≤ r ^ 2` and `dist y x ≤ |r|`;

  * from the sup distance to the sum of squares: the sum is at most `n ε^2`, and taking
    `ε = |r| / (n+1)` gives `n ε^2 ≤ r^2` because `n ≤ (n+1)^2`.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Work.WilG1.Calc

/-- If the sum of squares of the coordinate differences of `y` and `x` is at most `r ^ 2`, then
the sup-distance is at most `|r|`. -/
lemma dist_le_abs_of_sum_sq_le {n : ℕ} {x y : Fin n → ℝ} {r : ℝ}
    (h : ∑ i : Fin n, (y i - x i) ^ 2 ≤ r ^ 2) : dist y x ≤ |r| := by
  refine (dist_pi_le_iff (abs_nonneg r)).mpr fun i => ?_
  have hterm : (y i - x i) ^ 2 ≤ ∑ j : Fin n, (y j - x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j - x j)) (Finset.mem_univ i)
  have h2 : (y i - x i) ^ 2 ≤ r ^ 2 := le_trans hterm h
  rw [Real.dist_eq]
  exact sq_le_sq.mp h2

/-- The arithmetic bound that turns `n` coordinate estimates of size `|r| / (n+1)` into a sum
of squares bounded by `r ^ 2`. -/
lemma card_mul_sq_div_le {n : ℕ} {r : ℝ} :
    (n : ℝ) * (|r| / ((n : ℝ) + 1)) ^ 2 ≤ r ^ 2 := by
  have hsq_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hkey : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg ((n : ℝ))
    nlinarith
  have h : (n : ℝ) * (|r| / ((n : ℝ) + 1)) ^ 2 =
      (n : ℝ) * |r| ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    rw [div_pow]; ring
  rw [h, sq_abs]
  rw [div_le_iff₀ hsq_pos]
  nlinarith [hkey, sq_nonneg r]

theorem closure_char {n : ℕ} (X : Set (Fin n → ℝ)) :
    closure X = {x : Fin n → ℝ | ∀ r : ℝ, r ≠ 0 → ∃ y ∈ X, ∑ i : Fin n, (y i - x i) ^ 2 ≤ r ^ 2} := by
  ext x
  constructor
  · -- `x ∈ closure X` gives, for every `r ≠ 0`, a point of `X` whose sup-distance to `x` is
    -- below `|r| / (n+1)`; its sum of squares is then at most `r ^ 2`.
    intro hx r hr
    have hεpos : 0 < |r| / ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos (abs_pos.mpr hr) h1
    obtain ⟨y, hyX, hy⟩ := (Metric.mem_closure_iff.mp hx) _ hεpos
    refine ⟨y, hyX, ?_⟩
    have hcoord : ∀ i : Fin n, (y i - x i) ^ 2 ≤ (|r| / ((n : ℝ) + 1)) ^ 2 := by
      intro i
      have h1 : dist (x i) (y i) < |r| / ((n : ℝ) + 1) := (dist_pi_lt_iff hεpos).mp hy i
      rw [Real.dist_eq] at h1
      have h2 : |y i - x i| ≤ |r| / ((n : ℝ) + 1) := by
        rw [abs_sub_comm]
        exact le_of_lt h1
      exact sq_le_sq.mpr (by rwa [abs_of_pos hεpos])
    calc ∑ i : Fin n, (y i - x i) ^ 2 ≤ ∑ _i : Fin n, (|r| / ((n : ℝ) + 1)) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (n : ℝ) * (|r| / ((n : ℝ) + 1)) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ r ^ 2 := card_mul_sq_div_le
  · -- Conversely a point satisfying the sum-of-squares criterion for every `r ≠ 0` is in the
    -- closure: take `r = ε / 2 > 0`.
    intro hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hhalf : (ε / 2) ≠ 0 := by positivity
    obtain ⟨y, hyX, hy⟩ := hx (ε / 2) hhalf
    refine ⟨y, hyX, ?_⟩
    have hle : dist y x ≤ |ε / 2| := dist_le_abs_of_sum_sq_le hy
    rw [abs_of_pos (by positivity : (0 : ℝ) < ε / 2)] at hle
    rw [dist_comm]
    linarith

end Work.WilG1.Calc
