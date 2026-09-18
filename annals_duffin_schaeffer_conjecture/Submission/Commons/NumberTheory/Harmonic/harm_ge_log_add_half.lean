import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A lower bound for the harmonic numbers

We prove, for every `R ≥ 1`,
`log R + 1/2 + 1/(2R) ≤ H_R`,
where `H_R = ∑_{i=1}^{R} 1/i` is the `R`-th harmonic number (`harmonic R` in Mathlib,
a rational number, cast here to `ℝ`).

This refines the classical estimate `H_R = log R + γ + O(1/R)`; the constant `1/2` is
optimal at `R = 1`, where equality holds.

The proof rests on the elementary inequality `log x ≤ (x - x⁻¹)/2` for `x ≥ 1`
(the hyperbolic sine bound `t ≤ sinh t`), applied to `x = (R+1)/R`, together with
induction on `R`.
-/

namespace Commons.NumberTheory.Harmonic

/-- For `x ≥ 1` we have `log x ≤ (x - x⁻¹) / 2`. This is the two-sided
("sinh") form of the naive logarithm bound. -/
lemma log_le_half_sub_inv (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  have h0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc Real.log x ≤ Real.sinh (Real.log x) := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
    _ = (x - x⁻¹) / 2 := Real.sinh_log h0

/-- The logarithmic increment `log (r+1) - log r` is at most the average of the
reciprocals `1/r` and `1/(r+1)`, for `r ≥ 1`. -/
lemma log_succ_sub_log_le (r : ℝ) (hr : 1 ≤ r) :
    Real.log (r + 1) - Real.log r ≤ 1/(2*r) + 1/(2*(r+1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h1 : (1:ℝ) ≤ (r + 1) / r := by
    rw [le_div_iff₀ hr0]; linarith
  have hA := log_le_half_sub_inv ((r+1)/r) h1
  have hlog : Real.log ((r+1)/r) = Real.log (r+1) - Real.log r :=
    Real.log_div (by linarith) (by linarith)
  rw [hlog] at hA
  have harith : (((r+1)/r) - ((r+1)/r)⁻¹) / 2 = 1/(2*r) + 1/(2*(r+1)) := by
    rw [inv_div]
    field_simp
    ring
  linarith [hA, harith.le, harith.ge]

/-- The harmonic numbers, cast to `ℝ`, as a sum of real reciprocals. -/
lemma harmonic_cast_eq_sum (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ Finset.range n, ((i + 1 : ℝ))⁻¹ := by
  rw [harmonic, Rat.cast_sum]
  push_cast
  rfl

theorem harm_ge_log_add_half (R : ℕ) (hR : 1 ≤ R) :
    Real.log (R : ℝ) + 1/2 + 1/(2 * R) ≤ (harmonic R : ℝ) := by
  have key : ∀ n : ℕ, 1 ≤ n → Real.log (n:ℝ) + 1/2 + 1/(2 * n) ≤ (harmonic n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [harmonic_cast_eq_sum 1, Finset.sum_range_one]
      norm_num
    | succ m hm ih =>
      rw [harmonic_cast_eq_sum m] at ih
      rw [harmonic_cast_eq_sum (m+1), Finset.sum_range_succ]
      have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hpos : (0:ℝ) < m := by linarith
      have hkey := log_succ_sub_log_le (m:ℝ) hmr
      have h2 : ((m:ℝ)+1)⁻¹ = 1/(2*((m:ℝ)+1)) + 1/(2*((m:ℝ)+1)) := by
        rw [inv_eq_one_div]
        field_simp
        ring
      push_cast
      rw [h2]
      linarith [ih, hkey]
  exact key R hR

end Commons.NumberTheory.Harmonic