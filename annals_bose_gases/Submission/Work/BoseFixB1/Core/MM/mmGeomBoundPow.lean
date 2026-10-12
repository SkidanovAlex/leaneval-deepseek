import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.MM.mmGeomBoundPow`

The geometric bound of the mean-mismatch step at the diluteness-correct
parameters `fsParams (μA³)`: the box-side/`d` combination

  `ℓ d = sideAt μ A · d = A (μA³)^{-157/323}`,   `d = (μA³)^{6/323}`

is rewritten in closed form and the logarithmic loss of the mean-mismatch
kernel is charged against the diluteness power `(μA³)^{468/323}` (this is the
form needed by the small-diluteness quantifier `mmExistsPowLe`).

The whole content is the scalar inequality `geom_core` below, whose proof uses
only `(1 - 6 log x)x ≤ 6e^{-5/6} ≤ 7` for `x ∈ (0,1]` (through
`Real.mul_exp_neg_le_exp_neg_one`).
-/

namespace Work.BoseFixB1.Core.MM

set_option autoImplicit false

/-- `(1 + 6v) e^{-v} ≤ 7` for `v ≥ 0`: the elementary bound `ve^{-v} ≤ e^{-1} ≤ 1`
controls the logarithmic loss `6v = 6(-log t)/323`. -/
lemma mmGeomBoundPow_exp (v : ℝ) (hv : 0 ≤ v) : (1 + 6 * v) * Real.exp (-v) ≤ 7 := by
  have h1 : Real.exp (-v) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h2 : v * Real.exp (-v) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one v
    have h3 : Real.exp (-1) ≤ (1 : ℝ) := by rw [Real.exp_le_one_iff]; norm_num
    linarith
  have h4 : (1 + 6 * v) * Real.exp (-v)
      = Real.exp (-v) + 6 * (v * Real.exp (-v)) := by ring
  rw [h4]; linarith

/-- **The logarithmic-loss bound**: for `0 < t ≤ 1` and `c > 0`,

  `(1 + c⁻¹ + (6/323)(-log t)) · t^{1/323} ≤ 7 + c⁻¹`.

Writing `t^{1/323} = e^{-v}` with `v = (-log t)/323 ≥ 0`, the left-hand side is
`(1 + c⁻¹ + 6v) e^{-v} ≤ (1 + 6v)e^{-v} + c⁻¹ ≤ 7 + c⁻¹`. -/
lemma mmGeomBoundPow_key {c t : ℝ} (hc : 0 < c) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + c⁻¹ + (6 / 323) * (-Real.log t)) * t ^ (1 / 323 : ℝ) ≤ 7 + c⁻¹ := by
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  set v : ℝ := -(Real.log t) / 323 with hvdef
  have hv : 0 ≤ v := by rw [hvdef]; linarith
  have hlog : Real.log t = -323 * v := by rw [hvdef]; ring
  have hbeta : t ^ (1 / 323 : ℝ) = Real.exp (-v) := by
    rw [Real.rpow_def_of_pos ht0]
    rw [show Real.log t * (1 / 323 : ℝ) = -v by rw [hlog]; ring]
  have hw : (6 / 323) * (-Real.log t) = 6 * v := by rw [hlog]; ring
  have hmain := mmGeomBoundPow_exp v hv
  have hexp1 : Real.exp (-v) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  rw [hbeta, hw]
  have ha : c⁻¹ * Real.exp (-v) ≤ c⁻¹ := by
    have := mul_le_mul_of_nonneg_left hexp1 hcinv.le
    simpa using this
  calc (1 + c⁻¹ + 6 * v) * Real.exp (-v)
      = (1 + 6 * v) * Real.exp (-v) + c⁻¹ * Real.exp (-v) := by ring
    _ ≤ 7 + c⁻¹ := add_le_add hmain ha

/-- **The scalar core**: for `c > 0` and `0 < t ≤ 1`,

  `(1 + (c t^{-157/323})⁻¹ + |log (t^{6/323})|)³ · ((c t^{-157/323})³)⁻¹
     ≤ (c⁻¹)³ (7 + c⁻¹)³ t^{468/323}`.

Indeed `c t^{-157/323} ≥ c`, so its inverse is at most `c⁻¹`, and
`|log (t^{6/323})| = (6/323)(-log t)`; the cube of the inverse is
`c^{-3} t^{471/323}`, and `key_bound` bounds the remaining factor times
`t^{1/323}`. -/
lemma mmGeomBoundPow_core {c t : ℝ} (hc : 0 < c) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + (c * t ^ (-(157 / 323) : ℝ))⁻¹ + |Real.log (t ^ (6 / 323 : ℝ))|) ^ 3
      * (((c * t ^ (-(157 / 323) : ℝ)) ^ 3))⁻¹
    ≤ (c⁻¹) ^ 3 * (7 + c⁻¹) ^ 3 * t ^ (468 / 323 : ℝ) := by
  set q : ℝ := c * t ^ (-(157 / 323) : ℝ) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have ht157 : (1 : ℝ) ≤ t ^ (-(157 / 323) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
  have hqinv : q⁻¹ ≤ c⁻¹ := by
    have hs : (t ^ (-(157 / 323) : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht157
    have hcpos : 0 < c⁻¹ := inv_pos.mpr hc
    calc q⁻¹ = (t ^ (-(157 / 323) : ℝ))⁻¹ * c⁻¹ := by rw [hq, mul_inv_rev]
      _ ≤ 1 * c⁻¹ := mul_le_mul_of_nonneg_right hs hcpos.le
      _ = c⁻¹ := one_mul _
  have hlogabs : |Real.log (t ^ (6 / 323 : ℝ))| = (6 / 323) * (-Real.log t) := by
    rw [Real.log_rpow ht0]
    have hlt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 323), abs_of_nonpos hlt]
  have hwpos : 0 ≤ (6 / 323) * (-Real.log t) := by
    have hlt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
    have : (0 : ℝ) ≤ -Real.log t := by linarith
    exact mul_nonneg (by norm_num) this
  have hs3 : ((t ^ (-(157 / 323) : ℝ)) ^ 3)⁻¹ = t ^ (471 / 323 : ℝ) := by
    rw [← Real.rpow_natCast (t ^ (-(157 / 323) : ℝ)) 3, ← Real.rpow_mul ht0.le]
    rw [← Real.rpow_neg ht0.le]
    congr 1
    norm_num
  have hq3 : (q ^ 3)⁻¹ = (c⁻¹) ^ 3 * t ^ (471 / 323 : ℝ) := by
    rw [hq, mul_pow, mul_inv_rev, hs3, ← inv_pow]
    ring
  have hstep : (1 + q⁻¹ + |Real.log (t ^ (6 / 323 : ℝ))|) ^ 3 * (q ^ 3)⁻¹
      ≤ (1 + c⁻¹ + (6 / 323) * (-Real.log t)) ^ 3
          * ((c⁻¹) ^ 3 * t ^ (471 / 323 : ℝ)) := by
    have hle : 1 + q⁻¹ + |Real.log (t ^ (6 / 323 : ℝ))|
        ≤ 1 + c⁻¹ + (6 / 323) * (-Real.log t) := by
      rw [hlogabs]; linarith
    have hnonneg : 0 ≤ 1 + q⁻¹ + |Real.log (t ^ (6 / 323 : ℝ))| := by
      have h : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
      have := abs_nonneg (Real.log (t ^ (6 / 323 : ℝ)))
      linarith
    have hle3 := pow_le_pow_left₀ hnonneg hle 3
    refine mul_le_mul hle3 (le_of_eq hq3) ?_ ?_
    · exact inv_nonneg.mpr (pow_nonneg hqpos.le 3)
    · exact pow_nonneg (by linarith [inv_pos.mpr hc, hwpos]) 3
  have hpow1 : (t ^ (1 / 323 : ℝ)) ^ 3 = t ^ (3 / 323 : ℝ) := by
    rw [← Real.rpow_natCast (t ^ (1 / 323 : ℝ)) 3, ← Real.rpow_mul ht0.le]
    congr 1; norm_num
  have hpow2 : t ^ (471 / 323 : ℝ) = t ^ (468 / 323 : ℝ) * t ^ (3 / 323 : ℝ) := by
    rw [← Real.rpow_add ht0]; congr 1; norm_num
  have hstep2 : (1 + c⁻¹ + (6 / 323) * (-Real.log t)) ^ 3
        * ((c⁻¹) ^ 3 * t ^ (471 / 323 : ℝ))
      = (c⁻¹) ^ 3 * t ^ (468 / 323 : ℝ)
        * ((1 + c⁻¹ + (6 / 323) * (-Real.log t)) * t ^ (1 / 323 : ℝ)) ^ 3 := by
    rw [hpow2, mul_pow, hpow1]
    ring
  have hkey := mmGeomBoundPow_key hc ht0 ht1
  have hbnonneg : 0 ≤ (1 + c⁻¹ + (6 / 323) * (-Real.log t)) * t ^ (1 / 323 : ℝ) :=
    mul_nonneg (by linarith [inv_pos.mpr hc, hwpos]) (Real.rpow_nonneg ht0.le _)
  have hX3 : ((1 + c⁻¹ + (6 / 323) * (-Real.log t)) * t ^ (1 / 323 : ℝ)) ^ 3
      ≤ (7 + c⁻¹) ^ 3 :=
    pow_le_pow_left₀ hbnonneg hkey 3
  calc (1 + q⁻¹ + |Real.log (t ^ (6 / 323 : ℝ))|) ^ 3 * (q ^ 3)⁻¹
      ≤ (1 + c⁻¹ + (6 / 323) * (-Real.log t)) ^ 3
          * ((c⁻¹) ^ 3 * t ^ (471 / 323 : ℝ)) := hstep
    _ = (c⁻¹) ^ 3 * t ^ (468 / 323 : ℝ)
          * ((1 + c⁻¹ + (6 / 323) * (-Real.log t)) * t ^ (1 / 323 : ℝ)) ^ 3 := hstep2
    _ ≤ (c⁻¹) ^ 3 * t ^ (468 / 323 : ℝ) * (7 + c⁻¹) ^ 3 := by
        apply mul_le_mul_of_nonneg_left hX3
        exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hc.le) 3) (Real.rpow_nonneg ht0.le _)
    _ = (c⁻¹) ^ 3 * (7 + c⁻¹) ^ 3 * t ^ (468 / 323 : ℝ) := by ring

theorem mmGeomBoundPow {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    (1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
        + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
      * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹
    ≤ (A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (468 / 323 : ℝ) := by
  set t : ℝ := μ * A ^ 3 with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := ht
  -- the closed form of `ℓ d` and of `d`
  have hdt : (Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A
      = A * t ^ (-(157 / 323) : ℝ) := by
    rw [htdef, Work.BoseFixB1.d_mul_sideAt_eq hA hμ]
    congr 1
    rw [Work.BoseBox.fsXp]
    norm_num
  have hd : (Work.BoseBox.paramsAt μ A).d = t ^ (6 / 323 : ℝ) := by
    rw [htdef, Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp]
  have hcore := mmGeomBoundPow_core (c := A) (t := t) hA ht0 ht1
  rw [show (Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d
        = A * t ^ (-(157 / 323) : ℝ) by rw [mul_comm]; exact hdt]
  rw [hd]
  rw [show (A ^ 3)⁻¹ = (A⁻¹) ^ 3 by rw [inv_pow]]
  exact hcore

end Work.BoseFixB1.Core.MM
