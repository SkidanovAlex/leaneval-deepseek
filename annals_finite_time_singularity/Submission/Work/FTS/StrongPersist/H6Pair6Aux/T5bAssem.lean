/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6Pair6Aux/T5bAssem` — the scalar arithmetic of the row `T5bRow`

The row `T5bRow` is assembled from per-term bounds of the shape

`|∫∫ (k,i)-th summand| ≤ if (k,i) = (0,0) then C₀(1+X)⁴(1+Y²)
   else C(b,k)C(a,i)·Cc·(C₄X(XY+Y²) + C₆Y(XY))`,

where `X = |f|_{ℋ⁴}`, `Y = |f|_{ℋ⁶}`.  This module contains the purely scalar arithmetic
that turns the sum of those bounds into `C·α^{-3}·(1+X)⁴·(1+Y²)`, via the two elementary
inequalities `X²Y ≤ (1+X)⁴(1+Y²)` and `XY² ≤ (1+X)⁴(1+Y²)`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `X ≤ (1+X)⁴` for `X ≥ 0`. -/
theorem pow_le_one_add_four {x : ℝ} (hx : 0 ≤ x) : x ≤ (1 + x) ^ 4 := by
  have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
  calc x ≤ 1 + x := by linarith
    _ = (1 + x) ^ 1 := by ring
    _ ≤ (1 + x) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)

/-- `X²Y ≤ (1+X)⁴(1+Y²)` for `X, Y ≥ 0`. -/
theorem sq_mul_le_one_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 * y ≤ (1 + x) ^ 4 * (1 + y ^ 2) := by
  have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
  have h2 : x ^ 2 ≤ (1 + x) ^ 4 := by
    have h3 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    exact le_trans h3 (pow_le_pow_right₀ hx1 (by norm_num))
  have hP : 0 ≤ (1 + x) ^ 4 := pow_nonneg (by linarith) 4
  have hP1 : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  by_cases hyl : y ≤ 1
  · have h5 : x ^ 2 * y ≤ x ^ 2 := by nlinarith [sq_nonneg x, hyl]
    calc x ^ 2 * y ≤ x ^ 2 := h5
      _ ≤ (1 + x) ^ 4 := h2
      _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) := le_mul_of_one_le_right hP hP1
  · have hy1 : 1 ≤ y := by linarith
    have h5 : x ^ 2 * y ≤ x ^ 2 * (y * y) := by
      have hyy : y ≤ y * y := by nlinarith [hy, hy1]
      exact mul_le_mul_of_nonneg_left hyy (sq_nonneg x)
    calc x ^ 2 * y ≤ x ^ 2 * (y * y) := h5
      _ = x ^ 2 * y ^ 2 := by ring
      _ ≤ (1 + x) ^ 4 * y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg y)
      _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hP

/-- `X·Y² ≤ (1+X)⁴(1+Y²)` for `X, Y ≥ 0`. -/
theorem mul_sq_le_one_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ^ 2 ≤ (1 + x) ^ 4 * (1 + y ^ 2) := by
  have h1 := pow_le_one_add_four hx
  have hP : 0 ≤ (1 + x) ^ 4 := pow_nonneg (by linarith) 4
  calc x * y ^ 2 ≤ (1 + x) ^ 4 * y ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg y)
    _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [sq_nonneg y]) hP

/-- **The sum of the per-term bounds.** -/
theorem t5bSumBound {C0 Cc C4 C6 X Y : ℝ} (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hC6 : 0 ≤ C6) (hX : 0 ≤ X) (hY : 0 ≤ Y) {a b : ℕ} (hab : a + b ≤ 6) :
    (∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
      (if k = 0 ∧ i = 0 then C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
       else 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))))
      ≤ 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
  have hB : 0 ≤ Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)) := by positivity
  have hA : 0 ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2) := by positivity
  have hM : (0 : ℝ) ≤ 4096 * 4096 := by norm_num
  have hstep : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      (if k = 0 ∧ i = 0 then C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
       else 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
    intro k hk i hi
    by_cases h00 : k = 0 ∧ i = 0
    · rw [if_pos h00]; linarith
    · rw [if_neg h00]; linarith
  refine le_trans (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi =>
    hstep k hk i hi) ?_
  have hconst : (∑ k ∈ Finset.range (b + 1), ∑ _i ∈ Finset.range (a + 1),
        (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))))
      = (((b + 1) * (a + 1) : ℕ) : ℝ)
        * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hconst]
  have hcard : (((b + 1) * (a + 1) : ℕ) : ℝ) ≤ 49 := by
    have hb : b ≤ 6 := by omega
    have ha : a ≤ 6 := by omega
    have h1 : (b + 1) * (a + 1) ≤ 49 := by nlinarith
    exact_mod_cast h1
  have hnn : 0 ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
      + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
    linarith
  exact mul_le_mul_of_nonneg_right hcard hnn

/-- **The final arithmetic of the row.** -/
theorem t5bFinalArith {C0 Cc C4 C6 X Y α : ℝ} (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hC6 : 0 ≤ C6) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hα : 0 < α) (hα1 : α ≤ 1) :
    49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + X) ^ 4 * (1 + Y ^ 2) := by
  set K : ℝ := (1 + X) ^ 4 * (1 + Y ^ 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; positivity
  have hB : Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)) ≤ Cc * (2 * C4 + C6) * K := by
    have h1 : C4 * X * (X * Y + Y * Y) = C4 * (X ^ 2 * Y + X * (Y * Y)) := by ring
    have h2 : C6 * Y * (X * Y) = C6 * (X * (Y * Y)) := by ring
    rw [h1, h2]
    have h3 : C4 * (X ^ 2 * Y + X * Y ^ 2) ≤ C4 * (K + K) := by
      refine mul_le_mul_of_nonneg_left ?_ hC4
      rw [hK]
      exact add_le_add (sq_mul_le_one_add hX hY) (mul_sq_le_one_add hX hY)
    have h4 : C6 * (X * Y ^ 2) ≤ C6 * K := by
      refine mul_le_mul_of_nonneg_left ?_ hC6
      rw [hK]
      exact mul_sq_le_one_add hX hY
    have h5 : (0 : ℝ) ≤ C4 * (K + K) := by positivity
    have h6 : (0 : ℝ) ≤ C6 * K := by positivity
    calc Cc * (C4 * (X ^ 2 * Y + X * (Y * Y)) + C6 * (X * (Y * Y)))
        ≤ Cc * (C4 * (K + K) + C6 * K) := by
          refine mul_le_mul_of_nonneg_left ?_ hCc; linarith
      _ = Cc * (2 * C4 + C6) * K := by ring
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h1 : (α⁻¹) ^ (3 : ℝ) = α ^ (-(3 : ℝ)) := by
      rw [Real.inv_rpow hα.le, Real.rpow_neg hα.le]
    rw [← h1]
    exact Real.one_le_rpow ((one_le_inv₀ hα).mpr hα1) (by norm_num)
  have hM : (0 : ℝ) ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by
    have h3 : (0 : ℝ) ≤ 2 * C4 + C6 := by linarith
    positivity
  have hKM : 0 ≤ C0 * K := by positivity
  have h1 : 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)) ≤ 49 * C0 * K := by
    rw [hK]
    exact le_of_eq (by ring)
  have h2 : 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by
    have h3 : 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
        = 49 * (4096 * 4096) * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
      ring
    rw [h3]
    calc 49 * (4096 * 4096) * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))
        ≤ 49 * (4096 * 4096) * (Cc * (2 * C4 + C6) * K) := by
          refine mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by ring
  have h4 : 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      = 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2))
        + 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
    ring
  rw [h4]
  refine le_trans (add_le_add h1 h2) ?_
  calc 49 * C0 * K + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K
      = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6)) * K := by ring
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * K := by
        nlinarith [hKnn]
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1)
          * ((1 + X) ^ 4 * (1 + Y ^ 2)) := by rw [hK]
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1)
          * (α ^ (-(3 : ℝ)) * ((1 + X) ^ 4 * (1 + Y ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (1 + X) ^ 4 * (1 + Y ^ 2) = 1 * ((1 + X) ^ 4 * (1 + Y ^ 2)) := by ring
          _ ≤ α ^ (-(3 : ℝ)) * ((1 + X) ^ 4 * (1 + Y ^ 2)) :=
              mul_le_mul_of_nonneg_right hα3 (by positivity)
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + X) ^ 4 * (1 + Y ^ 2) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
