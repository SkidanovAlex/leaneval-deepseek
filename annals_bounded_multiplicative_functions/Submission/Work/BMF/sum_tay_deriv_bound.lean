import Mathlib
import Submission.Work.BMF.adi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- Closed form for the derivative of the `j`-th Taylor polynomial:
`Tay_j'(t) - 1/t = -(1/t) * (-(t-x)/x)^j`.  (For `j = 0`, `Tay_0 = 0` and both sides are
`-1/t`.) -/
theorem tay_deriv_sub_inv (j : ℕ) {x t : ℝ} (hx : x ≠ 0) (ht : t ≠ 0) :
    (Tay j x).derivative.eval t - 1 / t = -(1 / t) * (-(t - x) / x) ^ j := by
  have hsum : (∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * (t - x) ^ (m - 1) / x ^ m) - 1 / t
      = -(1 / t) * (-(t - x) / x) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      have hre : ((∑ k ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (k - 1) * (t - x) ^ (k - 1) / x ^ k) +
          ((-1 : ℝ) ^ (j + 1 - 1) * (t - x) ^ (j + 1 - 1) / x ^ (j + 1))) - 1 / t
          = ((∑ k ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (k - 1) * (t - x) ^ (k - 1) / x ^ k) - 1 / t) +
            ((-1 : ℝ) ^ (j + 1 - 1) * (t - x) ^ (j + 1 - 1) / x ^ (j + 1)) := by ring
      rw [hre, ih]
      have hg : 1 / x - 1 / t = -(1 / t) * (-(t - x) / x) := by field_simp
      have h1 : (-1 : ℝ) ^ (j + 1 - 1) * (t - x) ^ (j + 1 - 1) / x ^ (j + 1)
          = (1 / x) * (-(t - x) / x) ^ j := by
        rw [Nat.add_sub_cancel, div_pow]
        have hneg : (-(t - x) : ℝ) ^ j = (-1) ^ j * (t - x) ^ j := by
          rw [show -(t - x) = (-1) * (t - x) by ring, mul_pow]
        rw [hneg]; field_simp; ring
      rw [h1]
      rw [show -(1 / t) * (-(t - x) / x) ^ j + 1 / x * (-(t - x) / x) ^ j
          = ((-(t - x) / x) ^ j) * (1 / x - 1 / t) by ring]
      rw [hg, pow_succ]
      ring
  rw [tay_derivative_eval j hx t]
  exact hsum

/-- Norm form of `tay_deriv_sub_inv` for positive `x`, `t`. -/
theorem abs_tay_deriv_sub_inv (j : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    |(Tay j x).derivative.eval t - 1 / t| = 1 / t * (|t - x| / x) ^ j := by
  rw [tay_deriv_sub_inv j (ne_of_gt hx) (ne_of_gt ht), abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / t), abs_pow, abs_div, abs_neg,
    abs_of_pos hx]

/-- Geometric-type bound: for `r ≥ 0`, `∑_{j=1}^{k} r^j ≤ k * max 1 (r^k)`. -/
theorem sum_pow_Icc_le_card_mul_max (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∑ j ∈ Finset.Icc 1 k, r ^ j ≤ (k : ℝ) * max 1 (r ^ k) := by
  have hterm : ∀ j ∈ Finset.Icc 1 k, r ^ j ≤ max 1 (r ^ k) := by
    intro j hj
    rcases le_total r 1 with h | h
    · exact le_trans (pow_le_one₀ hr h) (le_max_left _ _)
    · exact le_trans (pow_le_pow_right₀ h (Finset.mem_Icc.mp hj).2) (le_max_right _ _)
  calc ∑ j ∈ Finset.Icc 1 k, r ^ j
      ≤ ∑ j ∈ Finset.Icc 1 k, max 1 (r ^ k) := Finset.sum_le_sum hterm
    _ = (Finset.Icc 1 k).card * max 1 (r ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (k : ℝ) * max 1 (r ^ k) := by rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem sum_tay_deriv_bound {k : ℕ} {x t δ : ℝ} (hx : 0 < x) (ht : 0 < t) (hδ : 0 ≤ δ)
    (htd : |t - x| ≤ δ) {T : ℕ → ℝ} {CT N : ℝ} (hN : 0 < N) (hCT : 0 ≤ CT)
    (hT : ∀ j ∈ Finset.Icc 1 k, |T j| ≤ CT * N ^ (j + 1)) :
    |∑ j ∈ Finset.Icc 1 k, T j / (2 * Real.pi) * ((Tay j x).derivative.eval t - 1 / t)| ≤
      ((k : ℝ) + 1) * CT * N / (2 * Real.pi * t) * max 1 ((N * δ / x) ^ k) := by
  -- per-term bound
  have hterm : ∀ j ∈ Finset.Icc 1 k,
      |T j / (2 * Real.pi) * ((Tay j x).derivative.eval t - 1 / t)|
        ≤ CT * N / (2 * Real.pi * t) * (N * δ / x) ^ j := by
    intro j hj
    have habs : |T j / (2 * Real.pi) * ((Tay j x).derivative.eval t - 1 / t)|
        = |T j| / (2 * Real.pi) * (1 / t * (|t - x| / x) ^ j) := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        abs_tay_deriv_sub_inv j hx ht]
    rw [habs]
    have hux : |t - x| / x ≤ δ / x := by
      rw [div_le_div_iff_of_pos_right hx]; exact htd
    have hpow : (|t - x| / x) ^ j ≤ (δ / x) ^ j :=
      pow_le_pow_left₀ (by positivity) hux j
    have hcd : 1 / t * (|t - x| / x) ^ j ≤ 1 / t * (δ / x) ^ j :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hle : |T j| / (2 * Real.pi) * (1 / t * (|t - x| / x) ^ j)
        ≤ CT * N ^ (j + 1) / (2 * Real.pi) * (1 / t * (δ / x) ^ j) :=
      mul_le_mul (div_le_div_of_nonneg_right (hT j hj) (by positivity)) hcd
        (by positivity) (by positivity)
    refine le_trans hle (le_of_eq ?_)
    rw [div_pow, div_pow, mul_pow, pow_succ]
    ring_nf
  have hstep1 : |∑ j ∈ Finset.Icc 1 k, T j / (2 * Real.pi) *
        ((Tay j x).derivative.eval t - 1 / t)|
      ≤ ∑ j ∈ Finset.Icc 1 k, CT * N / (2 * Real.pi * t) * (N * δ / x) ^ j :=
    le_trans
      (Finset.abs_sum_le_sum_abs
        (fun j => T j / (2 * Real.pi) * ((Tay j x).derivative.eval t - 1 / t))
        (Finset.Icc 1 k))
      (Finset.sum_le_sum hterm)
  have hC : 0 ≤ CT * N / (2 * Real.pi * t) := by positivity
  have hr : 0 ≤ N * δ / x := by positivity
  have hgeom := sum_pow_Icc_le_card_mul_max k hr
  have hstep2 : ∑ j ∈ Finset.Icc 1 k, CT * N / (2 * Real.pi * t) * (N * δ / x) ^ j
      ≤ ((k : ℝ) + 1) * CT * N / (2 * Real.pi * t) * max 1 ((N * δ / x) ^ k) := by
    calc ∑ j ∈ Finset.Icc 1 k, CT * N / (2 * Real.pi * t) * (N * δ / x) ^ j
        = CT * N / (2 * Real.pi * t) * ∑ j ∈ Finset.Icc 1 k, (N * δ / x) ^ j :=
          (Finset.mul_sum (Finset.Icc 1 k) (fun j => (N * δ / x) ^ j)
            (CT * N / (2 * Real.pi * t))).symm
      _ ≤ CT * N / (2 * Real.pi * t) * ((k : ℝ) * max 1 ((N * δ / x) ^ k)) :=
          mul_le_mul_of_nonneg_left hgeom hC
      _ = (k : ℝ) * (CT * N / (2 * Real.pi * t) * max 1 ((N * δ / x) ^ k)) := by ring
      _ ≤ ((k : ℝ) + 1) * (CT * N / (2 * Real.pi * t) * max 1 ((N * δ / x) ^ k)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = ((k : ℝ) + 1) * CT * N / (2 * Real.pi * t) * max 1 ((N * δ / x) ^ k) := by ring
  exact le_trans hstep1 hstep2

end Work.BMF
