import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate

namespace Work.Bottcher.Contraction

/-- On the far region `‖w‖ ≥ 32 (1 + ‖c‖)^4 + 32` the correction term
`normFactor c w - 1 = 2 c̄/w² + (c̄² + c)/w⁴` is at most `1/4`, so that in
particular the logarithm is controlled by `‖log 1+z‖ ≤ ‖z‖²(1-‖z‖)⁻¹/2 + ‖z‖`. -/
private theorem normFactor_sub_one_le_quarter (c w : ℂ)
    (hw : 32 * (1 + ‖c‖) ^ 4 + 32 ≤ ‖w‖) :
    2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 ≤ 1 / 2 := by
  have hwpos : (0:ℝ) < ‖w‖ := by
    have : (0:ℝ) ≤ (1 + ‖c‖) ^ 4 := by positivity
    linarith
  have hS1 : 2 * ‖c‖ / ‖w‖ ^ 2 ≤ 1 / 4 := by
    have ht1 : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
    have hW : 32 * (1 + ‖c‖) ^ 4 ≤ ‖w‖ := by linarith
    have ht_le_t8 : (1 + ‖c‖) ≤ (1 + ‖c‖) ^ 8 := by
      simpa using pow_le_pow_right₀ ht1 (by norm_num : (1:ℕ) ≤ 8)
    have hW2 : (32 * (1 + ‖c‖) ^ 4) ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hW 2
    have hid : (32 * (1 + ‖c‖) ^ 4) ^ 2 = 1024 * (1 + ‖c‖) ^ 8 := by ring
    have h8 : 8 * ‖c‖ ≤ ‖w‖ ^ 2 := by
      have hh : 8 * (1 + ‖c‖) ≤ 1024 * (1 + ‖c‖) ^ 8 := by nlinarith [ht_le_t8, ht1]
      nlinarith [norm_nonneg c]
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    linarith
  have hS2 : (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 ≤ 1 / 4 := by
    have ht1 : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
    have hW : 32 * (1 + ‖c‖) ^ 4 ≤ ‖w‖ := by linarith
    have ht2_le_t16 : (1 + ‖c‖) ^ 2 ≤ (1 + ‖c‖) ^ 16 :=
      pow_le_pow_right₀ ht1 (by norm_num : (2:ℕ) ≤ 16)
    have hW4 : (32 * (1 + ‖c‖) ^ 4) ^ 4 ≤ ‖w‖ ^ 4 := pow_le_pow_left₀ (by positivity) hW 4
    have hid : (32 * (1 + ‖c‖) ^ 4) ^ 4 = 1048576 * (1 + ‖c‖) ^ 16 := by ring
    have h4 : 4 * (‖c‖ ^ 2 + ‖c‖) ≤ ‖w‖ ^ 4 := by
      have hA : 4 * (‖c‖ ^ 2 + ‖c‖) ≤ 8 * (1 + ‖c‖) ^ 2 := by nlinarith [norm_nonneg c]
      have hB : 8 * (1 + ‖c‖) ^ 2 ≤ 1048576 * (1 + ‖c‖) ^ 16 := by
        nlinarith [ht2_le_t16, ht1]
      nlinarith
    rw [div_le_iff₀ (pow_pos hwpos 4)]
    linarith
  linarith

/-- **Second-order bound for `log` of the normalised Böttcher factor on the far
region.**  Writing `normFactor c w = 1 + u` with
`u = 2 c̄/w² + (c̄² + c)/w⁴`, the Taylor estimate `‖log 1+u‖ ≤ ‖u‖ + ‖u‖²`
for `‖u‖ ≤ 1/2` gives the stated bound. -/
theorem norm_log_normFactor_le (c w : ℂ) (hw : 32 * (1 + ‖c‖) ^ 4 + 32 ≤ ‖w‖) :
    ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ 2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4
        + 2 * (2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4) ^ 2 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    have : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
    have : (0 : ℝ) < (1 + ‖c‖) ^ 4 := pow_pos (by linarith [norm_nonneg c]) 4
    linarith
  have hsplit : Work.Bottcher.normFactor c w - 1
      = 2 * conj c / w ^ 2 + ((conj c) ^ 2 + c) / w ^ 4 := by
    rw [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply]
    field_simp
    ring
  have hu : ‖Work.Bottcher.normFactor c w - 1‖
      ≤ 2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by
    rw [hsplit]
    have hA : ‖2 * conj c / w ^ 2‖ = 2 * ‖c‖ / ‖w‖ ^ 2 := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_conj]
      norm_num
    have hB : ‖((conj c) ^ 2 + c) / w ^ 4‖ ≤ (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by
      rw [norm_div, norm_pow]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
    calc ‖2 * conj c / w ^ 2 + ((conj c) ^ 2 + c) / w ^ 4‖
        ≤ ‖2 * conj c / w ^ 2‖ + ‖((conj c) ^ 2 + c) / w ^ 4‖ := norm_add_le _ _
      _ ≤ 2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by
          rw [hA]; exact add_le_add le_rfl hB
  have hShalf := normFactor_sub_one_le_quarter c w hw
  have hu12 : ‖Work.Bottcher.normFactor c w - 1‖ ≤ 1 / 2 := le_trans hu hShalf
  have hlog := Complex.norm_log_one_add_le (z := Work.Bottcher.normFactor c w - 1)
    (lt_of_le_of_lt hu12 (by norm_num))
  have h1m : (1 - ‖Work.Bottcher.normFactor c w - 1‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hrew : (1 : ℂ) + (Work.Bottcher.normFactor c w - 1) = Work.Bottcher.normFactor c w := by
    ring
  rw [hrew] at hlog
  have hsq : ‖Work.Bottcher.normFactor c w - 1‖ ^ 2 * (1 - ‖Work.Bottcher.normFactor c w - 1‖)⁻¹ / 2
      ≤ (2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4) ^ 2 := by
    have hn0 : (0:ℝ) ≤ ‖Work.Bottcher.normFactor c w - 1‖ ^ 2 := by positivity
    have hstep : ‖Work.Bottcher.normFactor c w - 1‖ ^ 2 * (1 - ‖Work.Bottcher.normFactor c w - 1‖)⁻¹ / 2
        ≤ ‖Work.Bottcher.normFactor c w - 1‖ ^ 2 := by
      have h := h1m
      nlinarith [hn0]
    exact hstep.trans (pow_le_pow_left₀ (norm_nonneg _) hu 2)
  nlinarith [hlog, hu, hsq, sq_nonneg (2 * ‖c‖ / ‖w‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4)]

end Work.Bottcher.Contraction
