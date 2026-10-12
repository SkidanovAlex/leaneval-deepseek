import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `c0Bound` — the constant-`c₀` domination at FS's parameters

The localisation/estimates of FS `sec:params` need a constant `C₀` that dominates
the dimensionless combination `(10/(π X) + 1)^3 + 1` uniformly in the diluteness
`t = μa³ ∈ (0,1]`, where `X = fsXp t 1 = t^{1/323}`.  Here we show that

`(10/(π X) + 1)^3 + 1 ≤ 1000 · fsXp t (-1) · t^{-1/4}`

for all `0 < t ≤ 1`.

The proof is bare arithmetic.  Writing `Y = fsXp t (-1) = X⁻¹ ≥ 1`:

* `Y` is large: `X ≤ 1` gives `Y ≥ 1`, hence `(Y * t^{-1/4}) ≥ Y^3`
  (this is exactly the monotonicity `fsXp_le_fsXp` applied to the exponents
  `-327/4 ≤ -3`, using `t^{-1/4} = Y^{323/4}`);
* `10/(π X) = (10/π) Y ≤ 4 Y` since `π > 3`, so `10/(π X) + 1 ≤ 5 Y`
  (using `Y ≥ 1`), and cubing gives `≤ 125 Y^3 + 1 ≤ 126 Y^3`;
* `126 Y^3 ≤ 1000 Y^3`.

This is FS's remark that at these parameters `C₀` is an absolute constant.
-/

namespace Work.BoseFixR.farRadCountAux

open Work.BoseBox

theorem c0Bound {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (10 / (Real.pi * Work.BoseBox.fsXp t 1) + 1) ^ 3 + 1
      ≤ 1000 * (Work.BoseBox.fsXp t (-1) * t ^ (-(1 / 4 : ℝ))) := by
  have hXpos : 0 < fsXp t 1 := fsXp_pos ht0
  have hXle : fsXp t 1 ≤ 1 := fsXp_le_one ht0 ht1 (by norm_num)
  have hYpos : 0 < fsXp t (-1) := fsXp_pos ht0
  -- `Y = fsXp t (-1) = X⁻¹ ≥ 1`
  have hYge : 1 ≤ fsXp t (-1) := by
    rw [show fsXp t (-1) = (fsXp t 1)⁻¹ from (fsXp_inv ht0 1).symm]
    exact (one_le_inv₀ hXpos).mpr hXle
  -- `10/(π X) = (10/π) Y ≤ 4 Y`, hence `10/(π X) + 1 ≤ 5 Y`
  have hL : 10 / (Real.pi * fsXp t 1) + 1 ≤ 5 * fsXp t (-1) := by
    have hpi : 10 / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have h1 : 10 / (Real.pi * fsXp t 1) = (10 / Real.pi) * fsXp t (-1) := by
      rw [show fsXp t (-1) = (fsXp t 1)⁻¹ from (fsXp_inv ht0 1).symm]
      field_simp
    rw [h1]
    nlinarith [hYge, mul_le_mul_of_nonneg_right hpi hYpos.le]
  -- cube and compare with `126 Y^3`
  have hcube : (10 / (Real.pi * fsXp t 1) + 1) ^ 3 + 1 ≤ 126 * (fsXp t (-1)) ^ 3 := by
    have hnn : (0:ℝ) ≤ 10 / (Real.pi * fsXp t 1) + 1 := by positivity
    have h5 : (5 * fsXp t (-1)) ^ 3 = 125 * (fsXp t (-1)) ^ 3 := by ring
    have h3 : (1:ℝ) ≤ (fsXp t (-1)) ^ 3 := one_le_pow₀ hYge
    have hp : (10 / (Real.pi * fsXp t 1) + 1) ^ 3 ≤ (5 * fsXp t (-1)) ^ 3 :=
      pow_le_pow_left₀ hnn hL 3
    rw [h5] at hp
    linarith
  -- `Y^3 = fsXp t (-3)` and `fsXp t (-327/4) = Y * t^{-1/4}`
  have e1 : (fsXp t (-1))^3 = fsXp t (-3) := by
    rw [fsXp_pow ht0.le]; norm_num
  have e2 : fsXp t (-(327/4 : ℝ)) = fsXp t (-1) * t ^ (-(1/4:ℝ)) := by
    have h : (-(327/4:ℝ))/323 = (-1)/323 + (-(1/4:ℝ)) := by norm_num
    dsimp [fsXp]
    rw [h, Real.rpow_add ht0]
  -- the monotonicity in the exponent: `Y^3 ≤ Y · t^{-1/4}`
  have hY3 : (fsXp t (-1))^3 ≤ fsXp t (-1) * t ^ (-(1/4:ℝ)) := by
    rw [e1, ← e2]
    exact fsXp_le_fsXp ht0 ht1 (by norm_num)
  have hfin : 126 * (fsXp t (-1))^3 ≤ 1000 * (fsXp t (-1) * t ^ (-(1/4:ℝ))) := by
    have h1 : 126 * (fsXp t (-1))^3 ≤ 1000 * (fsXp t (-1))^3 := by
      have := pow_pos hYpos 3
      nlinarith
    have h2 : 1000 * (fsXp t (-1))^3 ≤ 1000 * (fsXp t (-1) * t ^ (-(1/4:ℝ))) :=
      mul_le_mul_of_nonneg_left hY3 (by norm_num)
    linarith
  linarith [hcube, hfin]

end Work.BoseFixR.farRadCountAux
