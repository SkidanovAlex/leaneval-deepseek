import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassCHon.CmpSupp.cmode_abs_le_of_continuous

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CmodeZero

/-- **The mode-`0` coefficient of a `C^∞` source compactly supported in the open quadrant is
bounded by a constant, uniformly in `z`.**

The source vanishes identically off its support rectangle `[a,b] × [c,d]`, so every slice
`G z ·` is identically zero for `z ∉ [a,b]` (whence `cmode 0 G z = 0`), while for `z ∈ [a,b]`
the Cauchy–Schwarz (Bessel) estimate for a continuous source bounds `cmode 0 G z` by a constant
times `1/√(eNorm 0)`; `eNorm 0 > 0` turns that into a constant. -/
theorem cmode_zero_abs_le_of_cptQ {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, |Work.FTS.PhiStar.Series.cmode 0 G z| ≤ K := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := hG.cpt
  -- joint continuity of the source
  have hcont : Continuous (Function.uncurry G) := (hG.smooth 0).continuous
  -- the source vanishes identically off the support rectangle
  have hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0 := by
    intro z θ hz
    by_contra hne
    exact hz (H z θ hne).1
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.ClassCHon.CmpSupp.cmode_abs_le_of_continuous hcont hsupp
  refine ⟨K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm 0),
    div_nonneg hKpos.le (Real.sqrt_nonneg _), fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · exact hK 0 z hz
  · -- outside the support rectangle the whole slice, hence the mode coefficient, vanishes
    have hfun : (fun θ : ℝ =>
          G z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hsupp z θ hz, zero_mul, zero_mul]
    have hzero : Work.FTS.PhiStar.Series.cmode 0 G z = 0 := by
      rw [Work.FTS.PhiStar.Series.cmode, hfun]
      simp
    rw [hzero, abs_zero]
    exact div_nonneg hKpos.le (Real.sqrt_nonneg _)

end Work.FTS.PhiStar.Honesty.CmodeZero
