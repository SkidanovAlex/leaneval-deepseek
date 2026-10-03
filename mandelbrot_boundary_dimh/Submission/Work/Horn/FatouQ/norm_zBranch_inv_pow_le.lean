import Mathlib
import Submission.Work.Horn.FatouQ.rpow_neg_eq_mul_rpow_inv
import Submission.Work.Horn.FatouQ.rpow_neg_one_add_div_le

namespace Work.Horn.FatouQ

theorem norm_zBranch_inv_pow_le {q : ℕ} {c z w : ℂ} (hq : 1 ≤ q) (hc : c ≠ 0) (hzq : z ^ q = c / w)
    (hw : 1 ≤ w.re) {m : ℕ} (hm1 : 1 ≤ m) (hmq : m ≤ q - 1) :
    ‖w‖⁻¹ * (‖z‖⁻¹) ^ m ≤ ‖w‖ ^ (-(1 : ℝ) / (q : ℝ)) * ‖c‖ ^ (-(m : ℝ) / (q : ℝ)) := by
  have hw1 : (1:ℝ) ≤ ‖w‖ := le_trans hw (Complex.re_le_norm w)
  have hwpos : (0:ℝ) < ‖w‖ := lt_of_lt_of_le one_pos hw1
  have hcpos : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have hsnn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpow : ‖z‖ ^ q = ‖c‖ / ‖w‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hzq
    simpa using h
  have hsz : (‖z‖⁻¹)^m = ‖z‖ ^ (-(m:ℝ)) := by
    rw [inv_pow, ← Real.rpow_natCast ‖z‖ m, ← Real.rpow_neg hsnn m]
  have hA : ‖z‖ ^ (-(m:ℝ)) = ‖w‖ ^ ((m:ℝ)/(q:ℝ)) * ‖c‖ ^ (-(m:ℝ)/(q:ℝ)) :=
    rpow_neg_eq_mul_rpow_inv hq hwpos hcpos hsnn hpow
  have hB : ‖w‖ ^ (-(1:ℝ) + (m:ℝ)/(q:ℝ)) ≤ ‖w‖ ^ (-(1:ℝ)/(q:ℝ)) :=
    rpow_neg_one_add_div_le hq hw1 hmq
  have hLHS : ‖w‖⁻¹ * (‖z‖⁻¹)^m = ‖w‖ ^ (-(1:ℝ) + (m:ℝ)/(q:ℝ)) * ‖c‖ ^ (-(m:ℝ)/(q:ℝ)) := by
    rw [hsz, hA, ← Real.rpow_neg_one ‖w‖, ← mul_assoc,
        ← Real.rpow_add hwpos (-(1:ℝ)) ((m:ℝ)/(q:ℝ))]
  rw [hLHS]
  exact mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hcpos.le _)

end Work.Horn.FatouQ
