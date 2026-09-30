import Mathlib
import Submission.Work.BMF.adi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- Reindex a sum over `Icc 1 j` as a sum over `range j`. -/
lemma sum_Icc_one_eq_sum_range (j : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 j, f m = ∑ i ∈ Finset.range j, f (i + 1) := by
  rw [← Finset.Ico_succ_right_eq_Icc 1 j, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_comm]

/-- The Taylor remainder bound for `log (1 + r)`, in the form needed below:
for `|r| ≤ 1/2`, the `j`-th Taylor polynomial `∑_{m=1}^{j} (-1)^{m-1} r^m / m` differs from
`log (1 + r)` by at most `2 |r|^{j+1}`. -/
lemma log_sub_taySum_le (j : ℕ) {r : ℝ} (hr : |r| ≤ 1/2) :
    |Real.log (1 + r) - ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m|
      ≤ 2 * |r| ^ (j + 1) := by
  have hr1 : |r| < 1 := by linarith [abs_nonneg r]
  -- Mathlib's estimate for `log (1 - x)` at `x = -r` gives `log (1 + r)`.
  have key := Real.abs_log_sub_add_sum_range_le (x := -r) (by rw [abs_neg]; exact hr1) j
  rw [abs_neg, sub_neg_eq_add] at key
  have hneg : (∑ i ∈ Finset.range j, (-r) ^ (i + 1) / (i + 1)) =
      -(∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m) := by
    rw [sum_Icc_one_eq_sum_range]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (-r) ^ (i + 1) = -((-1 : ℝ) ^ i * r ^ (i + 1)) := by
      rw [show (-r) = (-1 : ℝ) * r by ring, mul_pow]
      have h2 : (-1 : ℝ) ^ (i + 1) = -(-1) ^ i := by rw [pow_succ]; ring
      rw [h2]; ring
    rw [h, show i + 1 - 1 = i from by omega]
    push_cast
    ring
  rw [hneg] at key
  rw [show -(∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m) + Real.log (1 + r)
        = Real.log (1 + r) - ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m from by
      ring] at key
  calc |Real.log (1 + r) - ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m|
      ≤ |r| ^ (j + 1) / (1 - |r|) := key
    _ ≤ 2 * |r| ^ (j + 1) := by
        have hpos : 0 < 1 - |r| := by linarith [abs_nonneg r]
        rw [div_le_iff₀ hpos]
        nlinarith [abs_nonneg r, pow_nonneg (abs_nonneg r) (j + 1)]

theorem abs_tay_sub_log_le {j : ℕ} {x u : ℝ} (hx : 0 < x) (hu : |u - x| ≤ x / 2) :
    |(Tay j x).eval u - Real.log (u / x)| ≤ 2 * (|u - x| / x) ^ (j + 1) := by
  set r : ℝ := (u - x) / x with hr
  have hx0 : x ≠ 0 := ne_of_gt hx
  -- `Tay j x` evaluated at `u` is the `j`-th Taylor polynomial of `log (1 + ·)` at `r`.
  have hTay : (Tay j x).eval u = ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m := by
    rw [tay_eval]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hr, div_pow]
    ring
  have hux : u / x = 1 + r := by
    rw [hr]
    field_simp
    ring
  have habs : |r| = |u - x| / x := by
    rw [hr, abs_div, abs_of_pos hx]
  have hrle : |r| ≤ 1 / 2 := by
    rw [habs, div_le_iff₀ hx]
    linarith
  have hcore := log_sub_taySum_le j hrle
  have h1 : |(Tay j x).eval u - Real.log (u / x)|
      = |Real.log (1 + r) - ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m| := by
    rw [hTay, hux, abs_sub_comm]
  rw [h1]
  calc |Real.log (1 + r) - ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * r ^ m / m|
      ≤ 2 * |r| ^ (j + 1) := hcore
    _ = 2 * (|u - x| / x) ^ (j + 1) := by rw [habs]

end Work.BMF
