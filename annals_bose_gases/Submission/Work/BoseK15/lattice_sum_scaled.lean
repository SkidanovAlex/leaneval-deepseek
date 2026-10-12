import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.small_part_scaled
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.lattice_sum_scaled` — the scaled lattice sum is `O(ℓ³)`

The box momenta are `ℓ⁻¹ • vec n`, `vec n = 2πn` the dual-lattice points of
`ℤ³` (`Work.BoseB4.vec`), so a mode sum `∑_q (1+‖k_q‖)^{-4}` becomes the lattice
sum `∑_{n} (1 + ‖vec n‖/ℓ)^{-4}`.  Here we bound *every* finite part of that
lattice sum by the explicit constant `520 ℓ³`, which is the volume scaling
`ℓ³∫(1+‖k‖)^{-4}dk = ℓ³/(6π²)` that FS §10 needs.

The estimate is the standard ball/tail split at radius `ℓ`:

* **inside the ball** (`‖vec n‖ < ℓ`): each summand is at most `1`, and
  `card_le_of_vec_norm_le` counts at most `(ℓ/π+1)³ ≤ (2ℓ)³ = 8ℓ³` lattice
  points — the piece `Work.BoseK15.small_part_scaled`;
* **outside the ball** (`‖vec n‖ ≥ ℓ`): writing `a = ‖vec n‖ ≥ ℓ ≥ 1`,
  `(1+a/ℓ)^{-4} = ℓ⁴/(ℓ+a)^4`, and `(1+a²)² ≤ 4(ℓ+a)^4` (because
  `1 + a² ≤ (ℓ+a)²`), so the summand is dominated by `4ℓ⁴ (1+a²)^{-2}`.  The
  explicit-constant tail bound `Work.BoseK15.sum_inv_one_add_norm_tail_const`
  (`s = 2`, `M = 1`) then gives `4ℓ⁴ · 128/ℓ = 512ℓ³`.

`8ℓ³ + 512ℓ³ = 520ℓ³`.  The split is sharp in the sense that the ball
contributes `≍ ℓ³` genuinely (its count grows like the volume) and the tail
contributes the same power of `ℓ` after the `ℓ⁴` scaling; only the leading
constants are crude (the count `card_le_of_vec_norm_le` is far from the true
volume constant), which is harmless because only existence of an absolute
constant is consumed downstream.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- `x^(-4) = (x⁴)⁻¹`: the bridge between the `rpow` form of the mode sum and the
integer-power form of the lattice decay sums. -/
private lemma rpow_neg_four (x : ℝ) (hx : 0 ≤ x) : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
  have h : x ^ (-(((4 : ℕ) : ℝ))) = (x ^ 4)⁻¹ := by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  exact h

/-- **Off the ball of radius `ℓ`**, the scaled summand is dominated by the
integrable lattice profile: for `a ≥ ℓ ≥ 1`,

    `(1 + a/ℓ)^{-4} = ℓ⁴/(ℓ+a)^4 ≤ 4ℓ⁴ (1+a²)^{-2}`.

Indeed `1 + a² ≤ (ℓ+a)²` (as `ℓ ≥ 1`, `a ≥ 0`), hence `(1+a²)² ≤ (ℓ+a)^4`. -/
private lemma term_le_div (ℓ a : ℝ) (hℓ : 1 ≤ ℓ) (ha : ℓ ≤ a) :
    (1 + a / ℓ) ^ (-(4 : ℝ)) ≤ 4 * ℓ ^ 4 * ((1 + a ^ 2) ^ 2)⁻¹ := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have ha0 : 0 ≤ a := le_trans (le_of_lt hℓpos) ha
  have hbase : 0 ≤ 1 + a / ℓ := by positivity
  -- the key inequality `(1+a²)² ≤ 4(ℓ+a)^4`
  have hkey : (1 + a ^ 2) ^ 2 ≤ 4 * (ℓ + a) ^ 4 := by
    have h1 : 1 + a ^ 2 ≤ (ℓ + a) ^ 2 := by nlinarith [hℓ, ha0, sq_nonneg ℓ]
    have h2 : ((ℓ + a) ^ 2) ^ 2 = (ℓ + a) ^ 4 := by ring
    have h3 : (1 + a ^ 2) ^ 2 ≤ ((ℓ + a) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [h2] at h3
    nlinarith [h3, show (0 : ℝ) ≤ (ℓ + a) ^ 4 by positivity]
  -- the summand as a quotient
  have hpow : (1 + a / ℓ) ^ 4 = (ℓ + a) ^ 4 / ℓ ^ 4 := by
    have h : (1 + a / ℓ) = (ℓ + a) / ℓ := by
      field_simp
    rw [h, div_pow]
  have hstep : (1 : ℝ) / (ℓ + a) ^ 4 ≤ 4 / (1 + a ^ 2) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using hkey
  calc (1 + a / ℓ) ^ (-(4 : ℝ))
      = ((1 + a / ℓ) ^ 4)⁻¹ := rpow_neg_four _ hbase
    _ = ((ℓ + a) ^ 4 / ℓ ^ 4)⁻¹ := by rw [hpow]
    _ = ℓ ^ 4 / (ℓ + a) ^ 4 := inv_div _ _
    _ = ℓ ^ 4 * (1 / (ℓ + a) ^ 4) := by rw [mul_one_div]
    _ ≤ ℓ ^ 4 * (4 / (1 + a ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 4 * ℓ ^ 4 * ((1 + a ^ 2) ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring

/-- **The `ℓ`-scaled lattice sum over any finite set of dual-lattice points is
`O(ℓ³)`**, with the explicit constant `520`. -/
theorem lattice_sum_scaled (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (S : Finset (Fin 3 → ℤ)) :
    (∑ n ∈ S, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) ≤ 520 * ℓ ^ 3 := by
  -- split `S` at the radius `ℓ`
  have hsplit : (∑ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
        (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)))
      + (∑ n ∈ S.filter (fun n => ¬ (ℓ ≤ ‖Work.BoseB4.vec n‖)),
        (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)))
      = (∑ n ∈ S, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) :=
    Finset.sum_filter_add_sum_filter_not S _ _
  rw [← hsplit]
  -- the tail: `512 ℓ³`
  have htail_part : (∑ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
        (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) ≤ 512 * ℓ ^ 3 := by
    have hb := sum_inv_one_add_norm_tail_const 2 1 (by norm_num) ℓ
      (S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖)) hℓ
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hpoint : ∀ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
        (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))
          ≤ 4 * ℓ ^ 4 * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹ :=
      fun n hn => term_le_div ℓ ‖Work.BoseB4.vec n‖ hℓ (Finset.mem_filter.mp hn).2
    calc (∑ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
            (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)))
        ≤ ∑ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
            4 * ℓ ^ 4 * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹ := Finset.sum_le_sum hpoint
      _ = 4 * ℓ ^ 4 * (∑ n ∈ S.filter (fun n => ℓ ≤ ‖Work.BoseB4.vec n‖),
            ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹) := by rw [Finset.mul_sum]
      _ ≤ 4 * ℓ ^ 4 * (128 / ℓ ^ 1) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 512 * ℓ ^ 3 := by field_simp; ring
  -- the ball: `8 ℓ³`
  have hsmall_part : (∑ n ∈ S.filter (fun n => ¬ (ℓ ≤ ‖Work.BoseB4.vec n‖)),
        (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) ≤ 8 * ℓ ^ 3 :=
    small_part_scaled ℓ hℓ _
      (fun n hn => lt_of_not_ge (Finset.mem_filter.mp hn).2)
  linarith

end Work.BoseK15
