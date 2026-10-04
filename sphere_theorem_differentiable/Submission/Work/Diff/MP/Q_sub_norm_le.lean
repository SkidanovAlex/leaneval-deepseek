import Mathlib
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Finset

/-!
# An elementary quadratic estimate for Hamilton's reaction term `Q`

`Submission.Diff.Alg.Q R` is the homogeneous quadratic polynomial in the entries of `R` given by
`Q(R)ᵢⱼₖₗ = ∑ₚ∑q (Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq - 2 Rᵢₚₗq Rⱼₚₖq)`.  Here we prove the Lipschitz
estimate used by the maximum-principle argument,

`‖Q R - Q T‖ ≤ 5 n² (‖R‖ + ‖T‖) ‖R - T‖`,

with the sup norm on `Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ`.  The proof is coordinatewise:
each of the three products in the summand of `Q` is expanded with
`a * b - c * d = a * (b - d) + (a - c) * d`, giving 5 products of two coordinate differences per
index pair `(p, q)` and `n ^ 2` index pairs.
-/

variable {n : ℕ}

/-- Elementary product-difference estimate: if `|a - c| ≤ e`, `|a| ≤ f`, `|d| ≤ g` and
`|b - d| ≤ e` then `|a * b - c * d| ≤ (f + g) * e`. -/
theorem abs_mul_sub_mul_le_add {a b c d e f g : ℝ} (h1 : |a - c| ≤ e) (h2 : |a| ≤ f)
    (h3 : |d| ≤ g) (h4 : |b - d| ≤ e) : |a * b - c * d| ≤ (f + g) * e := by
  have he : 0 ≤ e := le_trans (abs_nonneg _) h1
  have hf : 0 ≤ f := le_trans (abs_nonneg _) h2
  have hg : 0 ≤ g := le_trans (abs_nonneg _) h3
  have hsplit : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  calc |a * b - c * d| = |a * (b - d) + (a - c) * d| := by rw [hsplit]
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = |a| * |b - d| + |a - c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ f * e + e * g :=
        add_le_add (mul_le_mul h2 h4 (abs_nonneg _) hf) (mul_le_mul h1 h3 (abs_nonneg _) he)
    _ = (f + g) * e := by ring

/-- Every coordinate of a difference of curvature arrays is bounded by its sup norm. -/
theorem abs_sub_coord_le (R T : Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    |R i j k l - T i j k l| ≤ ‖R - T‖ := by
  have h : R i j k l - T i j k l = (R - T) i j k l := rfl
  rw [h]
  exact coord_le_norm (R - T) i j k l

/-- Coordinatewise form of the quadratic estimate: each coordinate of `Q R - Q T` is bounded by
`n ^ 2` times the sum over the `5` products of the per-index-pair bound
`(‖R‖ + ‖T‖) * ‖R - T‖`. -/
theorem Q_sub_coord_le (n : ℕ) (R T : Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    |(Submission.Diff.Alg.Q R - Submission.Diff.Alg.Q T) i j k l| ≤
      (n : ℝ) * ((n : ℝ) * (5 * ((‖R‖ + ‖T‖) * ‖R - T‖))) := by
  set C : ℝ := (‖R‖ + ‖T‖) * ‖R - T‖ with hC
  have hQ : (Submission.Diff.Alg.Q R - Submission.Diff.Alg.Q T) i j k l
      = ∑ p, ∑ q, ((R i j p q * R k l p q + 2 * R i p k q * R j p l q
            - 2 * R i p l q * R j p k q)
          - (T i j p q * T k l p q + 2 * T i p k q * T j p l q
            - 2 * T i p l q * T j p k q)) := by
    simp only [Submission.Diff.Alg.Q, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_sub_distrib]
  rw [hQ]
  have hpair : ∀ p q : Fin n,
      |(R i j p q * R k l p q + 2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q)
        - (T i j p q * T k l p q + 2 * T i p k q * T j p l q
          - 2 * T i p l q * T j p k q)| ≤ 5 * C := by
    intro p q
    set D1 : ℝ := R i j p q * R k l p q - T i j p q * T k l p q with hD1def
    set D2 : ℝ := R i p k q * R j p l q - T i p k q * T j p l q with hD2def
    set D3 : ℝ := R i p l q * R j p k q - T i p l q * T j p k q with hD3def
    have hbd1 : |D1| ≤ C := by
      rw [hD1def, hC]
      exact abs_mul_sub_mul_le_add (abs_sub_coord_le R T i j p q) (coord_le_norm R i j p q)
        (coord_le_norm T k l p q) (abs_sub_coord_le R T k l p q)
    have hbd2 : |D2| ≤ C := by
      rw [hD2def, hC]
      exact abs_mul_sub_mul_le_add (abs_sub_coord_le R T i p k q) (coord_le_norm R i p k q)
        (coord_le_norm T j p l q) (abs_sub_coord_le R T j p l q)
    have hbd3 : |D3| ≤ C := by
      rw [hD3def, hC]
      exact abs_mul_sub_mul_le_add (abs_sub_coord_le R T i p l q) (coord_le_norm R i p l q)
        (coord_le_norm T j p k q) (abs_sub_coord_le R T j p k q)
    have hsplit : (R i j p q * R k l p q + 2 * R i p k q * R j p l q
          - 2 * R i p l q * R j p k q)
        - (T i j p q * T k l p q + 2 * T i p k q * T j p l q
          - 2 * T i p l q * T j p k q) = D1 + 2 * D2 - 2 * D3 := by
      rw [hD1def, hD2def, hD3def]
      ring
    rw [hsplit]
    have h2 : |2 * D2| ≤ 2 * C := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hbd2 (by norm_num)
    have h3 : |2 * D3| ≤ 2 * C := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hbd3 (by norm_num)
    have h1 : |D1 + 2 * D2 - 2 * D3| ≤ |D1 + 2 * D2| + |2 * D3| := by
      simpa using abs_sub_le (D1 + 2 * D2) 0 (2 * D3)
    have h0 : |D1 + 2 * D2| ≤ |D1| + |2 * D2| := abs_add_le _ _
    linarith
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpair p q) ?_
  rw [show (∑ _p : Fin n, ∑ _q : Fin n, (5 : ℝ) * C)
      = (n : ℝ) * ((n : ℝ) * (5 * C)) from by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]

/-- Elementary quadratic estimate for Hamilton's reaction term `Q` (a homogeneous quadratic
polynomial in the entries of `R`), with an explicit constant: five products per index pair
`(p,q)` and `n ^ 2` pairs. Each coordinate of the difference is bounded using
`Work.Diff.MP.coord_le_norm` (every coordinate is bounded by the operator norm), and the nested
sup norm is handled by `Work.Diff.MP.norm_pi_le`. -/
theorem Q_sub_norm_le (n : ℕ) (R T : Submission.Diff.Alg.Curv4 n) :
    ‖Submission.Diff.Alg.Q R - Submission.Diff.Alg.Q T‖ ≤
      5 * (n : ℝ) ^ 2 * (‖R‖ + ‖T‖) * ‖R - T‖ := by
  have hnn : 0 ≤ 5 * (n : ℝ) ^ 2 * (‖R‖ + ‖T‖) * ‖R - T‖ := by positivity
  refine norm_pi_le _ hnn (fun i => norm_pi_le _ hnn (fun j => norm_pi_le _ hnn (fun k =>
    norm_pi_le _ hnn (fun l => ?_))))
  have h := Q_sub_coord_le n R T i j k l
  have hr : (n : ℝ) * ((n : ℝ) * (5 * ((‖R‖ + ‖T‖) * ‖R - T‖))) =
      5 * (n : ℝ) ^ 2 * (‖R‖ + ‖T‖) * ‖R - T‖ := by ring
  rw [hr] at h
  simpa using h

end Work.Diff.MP
