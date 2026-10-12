import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- `t ^ p * log (1 / t)` is dominated by `(2 / (p - q)) * t ^ q` for `0 < t ≤ 1` and
`q < p`.  This is the elementary "`log` is slower than any positive power" bound, proved
from `Real.log_le_rpow_div` at exponent `p - q`: multiplying by `t ^ p` turns the right
side into `t ^ q / (p - q)`, and `1 ≤ 2` gives the constant. -/
theorem rpow_mul_log_inv_le {t p q : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (h : q < p) :
    t ^ p * Real.log (1 / t) ≤ (2 / (p - q)) * t ^ q := by
  have ha : 0 < p - q := sub_pos.mpr h
  have hinv : 0 < 1 / t := by positivity
  have hlog : Real.log (1 / t) ≤ (1 / t) ^ (p - q) / (p - q) :=
    Real.log_le_rpow_div hinv.le ha
  have hp : 0 < t ^ p := Real.rpow_pos_of_pos ht0 p
  have step : t ^ p * Real.log (1 / t) ≤ t ^ p * ((1 / t) ^ (p - q) / (p - q)) :=
    mul_le_mul_of_nonneg_left hlog hp.le
  have hinvpow : (1 / t) ^ (p - q) = (t ^ (p - q))⁻¹ := by
    rw [one_div, Real.inv_rpow ht0.le]
  have hkey : t ^ p * (1 / t) ^ (p - q) = t ^ q := by
    rw [hinvpow, ← Real.rpow_neg ht0.le (p - q), ← Real.rpow_add ht0 p (-(p - q))]
    congr 1
    ring
  have hfin : t ^ p * ((1 / t) ^ (p - q) / (p - q)) = t ^ q / (p - q) := by
    rw [← mul_div_assoc, hkey]
  rw [hfin] at step
  refine le_trans step ?_
  rw [div_le_iff₀ ha]
  have hc : 2 / (p - q) * t ^ q * (p - q) = 2 * t ^ q := by
    field_simp
  rw [hc]
  linarith [Real.rpow_pos_of_pos ht0 q]

end Work.BoseBogFS
