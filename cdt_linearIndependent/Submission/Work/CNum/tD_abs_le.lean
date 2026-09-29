import Mathlib
import Submission.Work.CNum.tD_aux

namespace Work.CNum

theorem tD_abs_le {m : ℕ} (hm : 1 ≤ m) {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) : ‖tD m ψ‖ ≤ u1J m := by
  set z : ℂ := (m : ℂ) * (wf ψ) ^ (m - 1) * tanf ψ / (1 + (wf ψ) ^ m) with hz
  have htd : tD m ψ = 24 * z.re := by
    simp only [tD, hz]
  have hnorm : ‖z‖ = (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ / ‖1 + (wf ψ) ^ m‖ := by
    rw [hz]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, norm_tanf]
  have hle_a : (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ ≤ (m : ℝ) * rJ ^ (m - 1) * uJ := by
    have hp : ‖wf ψ‖ ^ (m - 1) ≤ rJ ^ (m - 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hψ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)) uJ_nonneg
  have hkey : |z.re| ≤ (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m) := by
    refine le_trans (Complex.abs_re_le_norm z) ?_
    rw [hnorm]
    exact div_le_div₀
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg rJ_nonneg _)) uJ_nonneg)
      hle_a (one_sub_rJ_pow_pos hm) (norm_one_add_pow_ge hψ)
  calc ‖tD m ψ‖ = 24 * |z.re| := by
        rw [htd, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 24)]
    _ ≤ 24 * ((m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m)) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = u1J m := by rw [u1J]; ring

end Work.CNum
