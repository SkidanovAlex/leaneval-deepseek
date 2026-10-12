import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.a0A2QJointNormScalar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.blockWeightA0A2Qimp` — the P-side block weight with the `+1/8` right-hand side

The target

    t (t − 1 − m)² / (16 (√(t+1) + √m)²)  ≤  (1/8)(t + 1 − m)² + 1/8        (t, m ≥ 0)

is the per-block `P`-side weight of the joint A0/A2 core in the form in which the assembly
consumes it.  Writing `X := (√(t+1) + √m)²` and clearing the (positive) denominator, it is
equivalent to the polynomial-in-`X` statement

    t (t − 1 − m)²  ≤  2 X ((t + 1 − m)² + 1) .

Three structural facts about `X` drive the proof (`u := t + 1 − m` is the shifted variable):

* `t ≤ X` and `t + 1 + m ≤ X` (the cross term `2√(t+1)√m ≥ 0`);
* `m ≥ t + 1 ⟹ 4 (t + 1) ≤ X` (monotonicity of `√·`).

Splitting on the sign of `u`:

* `u ≥ 2`: `(u−2)² ≤ u²`, and `t ≤ X` finishes (`X u² ≤ 2X(u²+1)`);
* `0 ≤ u ≤ 2`: `(u−2)² ≤ 4`, and the exact identity
  `(u + 2m)(u²+1) − 2(u + m − 1) = (u−1)²(u+2) + 2u + 2mu² ≥ 0` combined with `u + 2m ≤ X`
  handles it;
* `u < 0`: with `v := m − t − 1 > 0` one has `(u−2)² = (v+2)² = (v²+1) + (4v+3)` and
  `4(t+1)(v²+1) − t(4v+3) = t(2v−1)² + 4(v²+1) ≥ 0`, so `t(4v+3) ≤ 4(t+1)(v²+1) ≤ X(v²+1)`,
  while `t(v²+1) ≤ X(v²+1)`; summing gives the claim.

The constant `1/8` cannot be improved beyond `5/64`-scale slack (the ratio
`LHS/RHS` has supremum `5/8`, approached as `t, m → ∞` with `t + 1 − m = −1/2`), but the above
chain is asymptotically lossless enough to close with the stated `1/8`.
-/

namespace Work.BoseFixB1S

theorem blockWeightA0A2Qimp {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    t * (t - 1 - m) ^ 2 / (16 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2)
      ≤ (1 / 8) * (t + 1 - m) ^ 2 + 1 / 8 := by
  set X : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 with hXdef
  have ha : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have hb : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  have hXpos : 0 < X := by rw [hXdef]; exact sqrtSumSq_pos ht hm
  have hXeq : X = Real.sqrt (t + 1) ^ 2 + 2 * Real.sqrt (t + 1) * Real.sqrt m + Real.sqrt m ^ 2 := by
    rw [hXdef]; ring
  have hprod : 0 ≤ 2 * Real.sqrt (t + 1) * Real.sqrt m := by positivity
  have htX : t ≤ X := by nlinarith [hXeq, ha]
  have hXsum : t + 1 + m ≤ X := by nlinarith [hXeq, ha, hb, hprod]
  have hX4 : t + 1 ≤ m → 4 * (t + 1) ≤ X := by
    intro htm
    have hle : Real.sqrt (t + 1) ≤ Real.sqrt m := Real.sqrt_le_sqrt htm
    have h2 : 2 * Real.sqrt (t + 1) ≤ Real.sqrt (t + 1) + Real.sqrt m := by linarith
    have hA : (2 * Real.sqrt (t + 1)) ^ 2 ≤ (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have hB : (2 * Real.sqrt (t + 1)) ^ 2 = 4 * (t + 1) := by rw [mul_pow, ha]; ring
    rw [hXdef, ← hB]; exact hA
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * X)]
  have hfin : ((1 / 8) * (t + 1 - m) ^ 2 + 1 / 8) * (16 * X)
      = 2 * X * ((t + 1 - m) ^ 2 + 1) := by ring
  rw [hfin]
  have key : t * (t - 1 - m) ^ 2 ≤ 2 * X * ((t + 1 - m) ^ 2 + 1) := by
    rcases le_total 2 (t + 1 - m) with hu2 | hu2
    · -- `u ≥ 2`
      have hsq : (t - 1 - m) ^ 2 ≤ (t + 1 - m) ^ 2 := by nlinarith
      have h1 : t * (t - 1 - m) ^ 2 ≤ X * (t + 1 - m) ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_right htX (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hsq hXpos.le)
      have h2 : X * (t + 1 - m) ^ 2 ≤ 2 * X * ((t + 1 - m) ^ 2 + 1) := by
        nlinarith [hXpos, sq_nonneg (t + 1 - m)]
      linarith
    · rcases le_total 0 (t + 1 - m) with hu0 | hu0
      · -- `0 ≤ u ≤ 2`
        have hsq : (t - 1 - m) ^ 2 ≤ 4 := by nlinarith
        have h4 : t * (t - 1 - m) ^ 2 ≤ 4 * t := by nlinarith [hsq, ht]
        have hmid : 2 * t ≤ (t + 1 + m) * ((t + 1 - m) ^ 2 + 1) := by
          have hid : (t + 1 + m) * ((t + 1 - m) ^ 2 + 1) - 2 * t
              = ((t + 1 - m) - 1) ^ 2 * ((t + 1 - m) + 2) + 2 * (t + 1 - m)
                + 2 * m * (t + 1 - m) ^ 2 := by ring
          have hnn : 0 ≤ ((t + 1 - m) - 1) ^ 2 * ((t + 1 - m) + 2) + 2 * (t + 1 - m)
                + 2 * m * (t + 1 - m) ^ 2 := by positivity
          linarith [hid, hnn]
        have h4X : 4 * t ≤ 2 * X * ((t + 1 - m) ^ 2 + 1) := by
          have hc : 2 * ((t + 1 + m) * ((t + 1 - m) ^ 2 + 1))
              ≤ 2 * (X * ((t + 1 - m) ^ 2 + 1)) := by
            nlinarith [hXsum, sq_nonneg (t + 1 - m)]
          linarith [hmid, hc]
        linarith [h4, h4X]
      · -- `u < 0`
        have huu : (t + 1 - m) ^ 2 = (m - t - 1) ^ 2 := by ring
        have hdd : (t - 1 - m) ^ 2 = ((m - t - 1) + 2) ^ 2 := by ring
        have htm : t + 1 ≤ m := by linarith
        have hX4' : 4 * (t + 1) ≤ X := hX4 htm
        have hident : 4 * (t + 1) * ((m - t - 1) ^ 2 + 1) - t * (4 * (m - t - 1) + 3)
            = t * (2 * (m - t - 1) - 1) ^ 2 + 4 * ((m - t - 1) ^ 2 + 1) := by ring
        have hnn : 0 ≤ t * (2 * (m - t - 1) - 1) ^ 2 + 4 * ((m - t - 1) ^ 2 + 1) := by
          positivity
        have hstep : t * (4 * (m - t - 1) + 3) ≤ 4 * (t + 1) * ((m - t - 1) ^ 2 + 1) := by
          linarith [hident, hnn]
        have hstep2 : 4 * (t + 1) * ((m - t - 1) ^ 2 + 1) ≤ X * ((m - t - 1) ^ 2 + 1) := by
          nlinarith [hX4', sq_nonneg (m - t - 1)]
        have hstep3 : t * ((m - t - 1) ^ 2 + 1) ≤ X * ((m - t - 1) ^ 2 + 1) := by
          nlinarith [htX, sq_nonneg (m - t - 1)]
        have hexp : t * ((m - t - 1) + 2) ^ 2
            = t * ((m - t - 1) ^ 2 + 1) + t * (4 * (m - t - 1) + 3) := by ring
        rw [hdd, huu, hexp]
        linarith [hstep, hstep2, hstep3]
  linarith [key]

end Work.BoseFixB1S
