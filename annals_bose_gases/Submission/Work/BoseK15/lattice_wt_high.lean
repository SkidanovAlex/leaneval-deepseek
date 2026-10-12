import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.lattice_wt_high` — the `‖vec n‖^{-2}`-weighted lattice sum outside the ball

FS §10 needs the lattice sum
`∑_{n ∈ T} (1 + ‖vec n‖/ℓ)^{-4} (‖vec n‖/ℓ)^{-2}` over the *high* modes
`‖vec n‖ ≥ ℓ` to be `O(ℓ³)`.  This is the tail companion of
`Work.BoseK15.lattice_wt_low` (the same weight over the low modes `‖vec n‖ < ℓ`).

Proof:

* for `n ∈ T` put `r = ‖vec n‖ ≥ ℓ ≥ 1`.  Then `r/ℓ ≥ 1`, so the negative power
  `(r/ℓ)^{-2} ≤ 1`, and the summand is at most `(1 + r/ℓ)^{-4}`;
* `(1 + r/ℓ)^{-4} = ℓ⁴/(ℓ+r)^4 ≤ ℓ⁴/r^4 ≤ 4ℓ⁴ (1+r²)^{-2}` (the last because
  `1 + r² ≤ (ℓ+r)²` for `ℓ ≥ 1`);
* the dyadic tail bound `Work.BoseK15.sum_inv_one_add_norm_tail_const` (`s = 2`,
  `M = 1`) gives `∑_{n∈T} (1+‖vec n‖²)^{-2} ≤ 128/ℓ`;
* hence the sum is at most `4ℓ⁴ · 128/ℓ = 512 ℓ³ ≤ 1000 ℓ³`.

Only existence of the absolute constant `1000` is ever consumed downstream.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- **Pointwise domination of the high-mode weight.**  For `ℓ ≥ 1` and
`r ≥ ℓ ≥ 1`,

    `(1 + r/ℓ)^{-4} (r/ℓ)^{-2} ≤ 4 ℓ⁴ (1 + r²)^{-2}`.

Indeed `(r/ℓ)^{-2} ≤ 1`, while `(1 + r/ℓ)^{-4} = ℓ⁴/(ℓ+r)^4 ≤ 4ℓ⁴(1+r²)^{-2}`
because `1 + r² ≤ (ℓ+r)²` (as `ℓ ≥ 1`, `r ≥ 0`) implies
`(1 + r²)² ≤ (ℓ+r)^4`. -/
private lemma wt_high_core (ℓ r : ℝ) (hℓ : 1 ≤ ℓ) (hr : ℓ ≤ r) :
    (1 + r / ℓ) ^ (-(4 : ℝ)) * (r / ℓ) ^ (-(2 : ℝ))
      ≤ 4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹ := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hrpos : 0 < r := lt_of_lt_of_le hℓpos hr
  have hr0 : 0 ≤ r := hrpos.le
  -- the first factor
  have hA : (1 + r / ℓ) ^ (-(4 : ℝ)) ≤ 4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹ := by
    have hbase : 0 ≤ 1 + r / ℓ := by positivity
    have hkey : (1 + r ^ 2) ^ 2 ≤ 4 * (ℓ + r) ^ 4 := by
      have h1 : 1 + r ^ 2 ≤ (ℓ + r) ^ 2 := by nlinarith [hℓ, hr0, sq_nonneg ℓ]
      have h2 : ((ℓ + r) ^ 2) ^ 2 = (ℓ + r) ^ 4 := by ring
      have h3 : (1 + r ^ 2) ^ 2 ≤ ((ℓ + r) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      rw [h2] at h3
      nlinarith [h3, show (0 : ℝ) ≤ (ℓ + r) ^ 4 by positivity]
    have hpow : (1 + r / ℓ) ^ (4 : ℝ) = (ℓ + r) ^ 4 / ℓ ^ 4 := by
      rw [Real.rpow_ofNat]
      have h : (1 + r / ℓ) = (ℓ + r) / ℓ := by field_simp
      rw [h, div_pow]
    have hstep : (1 : ℝ) / (ℓ + r) ^ 4 ≤ 4 / (1 + r ^ 2) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using hkey
    calc (1 + r / ℓ) ^ (-(4 : ℝ))
        = ((1 + r / ℓ) ^ 4)⁻¹ := Real.rpow_neg hbase 4
      _ = ((ℓ + r) ^ 4 / ℓ ^ 4)⁻¹ := by rw [hpow]
      _ = ℓ ^ 4 / (ℓ + r) ^ 4 := inv_div _ _
      _ = ℓ ^ 4 * (1 / (ℓ + r) ^ 4) := by rw [mul_one_div]
      _ ≤ ℓ ^ 4 * (4 / (1 + r ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring
  -- the second factor
  have hB : (r / ℓ) ^ (-(2 : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
    rw [le_div_iff₀ hℓpos]
    linarith
  have hBnn : 0 ≤ (r / ℓ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hAnn : 0 ≤ 4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹ := by positivity
  calc (1 + r / ℓ) ^ (-(4 : ℝ)) * (r / ℓ) ^ (-(2 : ℝ))
      ≤ (4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹) * 1 := mul_le_mul hA hB hBnn hAnn
    _ = 4 * ℓ ^ 4 * ((1 + r ^ 2) ^ 2)⁻¹ := by ring

/-- **The `‖vec n‖^{-2}`-weighted lattice sum over the high modes is `O(ℓ³)`.**

For `ℓ ≥ 1` and a finite set `T` of lattice indices all of whose momenta satisfy
`ℓ ≤ ‖vec n‖` (FS's *high* mode region, the tail `‖q‖ ≳ ℓ` of the mode set),

    `∑_{n ∈ T} (1 + ‖vec n‖/ℓ)^{-4} (‖vec n‖/ℓ)^{-2} ≤ 1000 ℓ³`. -/
theorem lattice_wt_high (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (T : Finset (Fin 3 → ℤ))
    (hhi : ∀ n ∈ T, ℓ ≤ ‖Work.BoseB4.vec n‖) :
    ∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
      (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)) ≤ 1000 * ℓ ^ 3 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hne : ℓ ≠ 0 := ne_of_gt hℓpos
  have hpt : ∀ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
      (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ))
        ≤ 4 * ℓ ^ 4 * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹ :=
    fun n hn => wt_high_core ℓ ‖Work.BoseB4.vec n‖ hℓ (hhi n hn)
  have htail := sum_inv_one_add_norm_tail_const 2 1 (by norm_num) ℓ T hℓ hhi
  calc ∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
        (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ))
      ≤ ∑ n ∈ T, 4 * ℓ ^ 4 * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹ :=
        Finset.sum_le_sum hpt
    _ = 4 * ℓ ^ 4 * ∑ n ∈ T, ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹ :=
        (Finset.mul_sum T (fun n => ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹) (4 * ℓ ^ 4)).symm
    _ ≤ 4 * ℓ ^ 4 * (128 / ℓ ^ 1) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 512 * ℓ ^ 3 := by
        field_simp
        ring
    _ ≤ 1000 * ℓ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
        nlinarith

end Work.BoseK15
