import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology

/-!
# `Work.FTS.StrongEps.Traces.sin_rpow_thShift_le`

The angular weight `sin(2θ)^{-γ}` (and its `e`-powers) changes by at most `e^{ε|e|}` under the
`θ`-shift `thShift θ p = arctan (tan θ · e^{-p})` whenever `|p| ≤ ε`.

The whole content is the two-sided bound

  `e^{-|p|} sin(2θ) ≤ sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)`

(`Work.FTS.StrongEps.sinTwo_thShift_bounds`), which says exactly that the ratio
`sin(2θ)/sin(2·thShift θ p)` lies in `[e^{-|p|}, e^{|p|}]`; its logarithm is therefore bounded by
`|p| ≤ ε` in absolute value, and `x ^ e = exp (e · log x)` for `x > 0` turns that into the
claimed `e^{ε|e|}` multiplicative factor.
-/

theorem sin_rpow_thShift_le (θ p ε e : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hε : 0 ≤ ε)
    (hp : |p| ≤ ε) :
    Real.sin (2 * θ) ^ e
      ≤ Real.exp (ε * |e|) * Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ e := by
  set s := Real.sin (2 * θ) with hsdef
  set s' := Real.sin (2 * Work.FTS.StrongEps.thShift θ p) with hs'def
  have hs : 0 < s := by
    rw [hsdef]; exact Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < s' := by
    rw [hs'def]
    exact Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  obtain ⟨hlo, hhi⟩ := Work.FTS.StrongEps.sinTwo_thShift_bounds (θ := θ) (p := p) hθ
  -- `hlo : exp (-|p|) * s ≤ s'`, `hhi : s' ≤ exp |p| * s`
  have hRpos : 0 < s / s' := div_pos hs hs'
  have hRge : Real.exp (-|p|) ≤ s / s' := by
    rw [le_div_iff₀ hs']
    calc Real.exp (-|p|) * s'
        ≤ Real.exp (-|p|) * (Real.exp |p| * s) :=
          mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
      _ = s := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hRle : s / s' ≤ Real.exp |p| := by
    rw [div_le_iff₀ hs']
    calc s = Real.exp |p| * (Real.exp (-|p|) * s) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp |p| * s' := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
  -- the logarithm of the ratio is bounded by `|p| ≤ ε`
  have hlog : |Real.log (s / s')| ≤ |p| := by
    rw [abs_le]
    exact ⟨by
        have h := Real.log_le_log (Real.exp_pos (-|p|)) hRge
        rwa [Real.log_exp] at h,
      by
        have h := Real.log_le_log hRpos hRle
        rwa [Real.log_exp] at h⟩
  have hmain : (s / s') ^ e ≤ Real.exp (ε * |e|) := by
    rw [Real.rpow_def_of_pos hRpos]
    refine Real.exp_le_exp.mpr ?_
    calc Real.log (s / s') * e ≤ |Real.log (s / s') * e| := le_abs_self _
      _ = |Real.log (s / s')| * |e| := abs_mul _ _
      _ ≤ |p| * |e| := mul_le_mul_of_nonneg_right hlog (abs_nonneg e)
      _ ≤ ε * |e| := mul_le_mul_of_nonneg_right hp (abs_nonneg e)
  have hspow : s ^ e = (s / s') ^ e * s' ^ e := by
    conv_lhs => rw [show s = (s / s') * s' from (div_mul_cancel₀ s hs'.ne').symm]
    rw [Real.mul_rpow hRpos.le hs'.le]
  rw [hspow]
  exact mul_le_mul_of_nonneg_right hmain (Real.rpow_pos_of_pos hs' e).le

end Work.FTS.StrongEps.Traces
