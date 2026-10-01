import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_defs

namespace Work.LinnikAreas.Density4.Udecay

open Filter

/-- The Abel boundary term tends to zero: `muRecipSum M · (M+1)^{-s} → 0` as `M → ∞` for `s > 0`.
`recip_bound` (imported here) bounds `|muRecipSum M|` uniformly, and `x^{-s} → 0` at `+∞`
(`tendsto_rpow_neg_atTop`) composed with `M ↦ (M:ℝ)+1` squeezes the product to `0`. -/
theorem tendsto_muRecip_mul_rpow {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto
      (fun M : ℕ => Commons.NumberTheory.Moebius.muRecipSum M * ((M : ℝ) + 1) ^ (-s))
      Filter.atTop (nhds 0) := by
  -- `|muRecipSum M|` is uniformly bounded, thanks to the exponential decay of `recip_bound`.
  have hbound : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |Commons.NumberTheory.Moebius.muRecipSum m| ≤ C := by
    obtain ⟨c, C, hc, hCpos, hC⟩ := recip_bound
    refine ⟨C, hCpos, ?_⟩
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [Commons.NumberTheory.Moebius.muRecipSum]
      exact hCpos.le
    · have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have h2 := hC (m:ℝ) h1
      rw [Work.LinnikAreas.Density4.muRecip, Nat.floor_natCast] at h2
      refine le_trans h2 ?_
      have hexp : Real.exp (-(c * Real.sqrt (Real.log (m:ℝ)))) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hlog : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg h1
        have hs' : 0 ≤ Real.sqrt (Real.log (m:ℝ)) := Real.sqrt_nonneg _
        nlinarith [mul_nonneg hc.le hs']
      calc C * Real.exp (-(c * Real.sqrt (Real.log (m:ℝ))))
          ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hCpos.le
        _ = C := mul_one C
  obtain ⟨C, hCpos, hC⟩ := hbound
  -- The power factor `(M+1)^{-s}` tends to `0` at `+∞`.
  have hrpow : Tendsto (fun M : ℕ => ((M:ℝ)+1)^(-s)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hs).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have hprod : Tendsto (fun M : ℕ => C * ((M:ℝ)+1)^(-s)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul hrpow
  -- Squeeze the product between `0` and `C · (M+1)^{-s}`.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun M : ℕ => C * ((M:ℝ)+1)^(-s))
    (fun M => abs_nonneg _) (fun M => ?_) hprod
  rw [Real.norm_eq_abs, abs_mul]
  have hpos : 0 < ((M:ℝ)+1)^(-s) := Real.rpow_pos_of_pos (by positivity) _
  rw [abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right (hC M) hpos.le

end Work.LinnikAreas.Density4.Udecay
