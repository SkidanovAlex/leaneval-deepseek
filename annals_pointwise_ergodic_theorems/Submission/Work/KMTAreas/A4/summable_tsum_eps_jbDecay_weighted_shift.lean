import Mathlib
import Submission.Work.Analysis.InverseTheory.calc_of_decay

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The `ε`-weighted, `|·|`-weighted kernel is dominated by the summable `p`-series
`(ε⁻¹)^11 · |u|^{-11}`.

Away from `u = 0` one has `|εu| ≤ ⟨εu⟩`, hence `⟨εu⟩^{-12} ≤ |εu|^{-12} = ε^{-12}|u|^{-12}`, and
multiplying by `ε |u|` produces `ε^{-11} |u|^{-11}`; at `u = 0` both sides vanish. -/
lemma eps_jbDecay_twelve_mul_abs_le {ε : ℝ} (hε0 : 0 < ε) (u : ℤ) :
    ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)| ≤ (ε⁻¹) ^ 11 * (1 / |(u : ℝ)| ^ (11 : ℝ)) := by
  rcases eq_or_ne (u : ℝ) 0 with hu | hu
  · rw [hu]
    simp
  · have ht : ε * (u : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hε0) hu
    have hle : (jb (ε * (u : ℝ)))⁻¹ ≤ (|ε * (u : ℝ)|)⁻¹ := by
      rw [inv_le_inv₀ (jb_pos _) (abs_pos.mpr ht)]
      exact abs_le_jb _
    have hpow : jbDecay 12 (ε * (u : ℝ)) ≤ ((|ε * (u : ℝ)|)⁻¹) ^ 12 := by
      rw [jbDecay]
      exact pow_le_pow_left₀ (jb_inv_nonneg _) hle 12
    have hstep : ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|
        ≤ ε * ((|ε * (u : ℝ)|)⁻¹) ^ 12 * |(u : ℝ)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hε0.le) (abs_nonneg _)
    refine hstep.trans_eq ?_
    have habs_mul : |ε * (u : ℝ)| = ε * |(u : ℝ)| := by rw [abs_mul, abs_of_pos hε0]
    have hrpow : (1 : ℝ) / |(u : ℝ)| ^ (11 : ℝ) = ((|(u : ℝ)|)⁻¹) ^ 11 := by
      rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, inv_pow]
    rw [hrpow, habs_mul, mul_inv, mul_pow]
    field_simp

/-- The `ℤ`-series `u ↦ ε ⟨εu⟩^{-12} |u|` is summable: the pointwise bound of
`eps_jbDecay_twelve_mul_abs_le` compares it with a constant multiple of the `p`-series
`|u|^{-11}`, which converges by `Real.summable_one_div_int_add_rpow`. -/
lemma summable_eps_jbDecay_twelve_mul_abs {ε : ℝ} (hε0 : 0 < ε) :
    Summable (fun u : ℤ => ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|) := by
  have hcomp : Summable (fun u : ℤ => (ε⁻¹) ^ 11 * (1 / |(u : ℝ)| ^ (11 : ℝ))) := by
    have h : Summable (fun u : ℤ => (1 : ℝ) / |(u : ℝ)| ^ (11 : ℝ)) := by
      have h := (Real.summable_one_div_int_add_rpow (0 : ℝ) (11 : ℝ)).mpr
        (by norm_num : (1 : ℝ) < 11)
      simpa using h
    exact h.mul_left ((ε⁻¹) ^ 11)
  exact Summable.of_nonneg_of_le
    (fun u => mul_nonneg (mul_nonneg hε0.le (jbDecay_nonneg 12 _)) (abs_nonneg _))
    (fun u => eps_jbDecay_twelve_mul_abs_le hε0 u) hcomp

/-- **Summability and translation invariance of the `ε`-weighted kernel.**

For `ε > 0` and any shift `y : ℤ`, the family
`m ↦ ε ⟨ε (m - y)⟩^{-12} |m - y|` is summable and its `ℤ`-sum is independent of `y`: the
substitution `u = m - y` (the group equivalence `Equiv.subRight y`) is a bijection of `ℤ`. -/
theorem summable_tsum_eps_jbDecay_weighted_shift {ε : ℝ} (hε0 : 0 < ε) (y : ℤ) :
    Summable (fun m : ℤ => ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)|) ∧
      (∑' m : ℤ, ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)|)
        = ∑' u : ℤ, ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)| := by
  have hsum : Summable (fun u : ℤ => ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|) :=
    summable_eps_jbDecay_twelve_mul_abs hε0
  refine ⟨?_, ?_⟩
  · refine ((Equiv.summable_iff
        (f := fun u : ℤ => ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|)
        (Equiv.subRight y)).mpr hsum).congr (fun m => ?_)
    simp only [Function.comp_apply, Equiv.subRight_apply]
    push_cast
    ring
  · rw [← Equiv.tsum_eq (Equiv.subRight y)
      (fun u : ℤ => ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|)]
    refine tsum_congr (fun m => ?_)
    simp only [Equiv.subRight_apply]
    push_cast
    ring

end Work.KMTAreas.A4
