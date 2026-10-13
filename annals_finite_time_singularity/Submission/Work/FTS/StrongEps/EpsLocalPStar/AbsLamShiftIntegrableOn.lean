import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Filter

/-- **The shifted absolute trace is integrable.**  If `u ↦ lam (exp u)` is integrable on the
line, then for every `z > 0` the function `x ↦ |lam (z * exp (-x))|` is integrable on the whole
line, hence on the interval `Icc (-ε) ε`.

The substitution `u = log z - x` is an affine (indeed, measure preserving) change of variable:
`z * exp (-x) = exp (log z - x)`, so the claim is the translation- and dilation-invariance of the
Lebesgue integral — no local structure of `lam` beyond the integrability of its log-trace is
needed.  (The sibling `mti_integrable_shift_abs` of `MarginalTransferIntegrable.lean` is the
ε-generalised form of the same computation, with `-(ε * x)` in place of `-x`; here the
`ε` only enters through the irrelevant interval `Icc (-ε) ε`.) -/
theorem AbsLamShiftIntegrableOn {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {ε z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun x : ℝ => |lam (z * Real.exp (-x))|) (Set.Icc (-ε) ε) := by
  -- (1) translate the log-trace by `log z`; the translation is measure preserving
  have h1 : MeasureTheory.Integrable (fun y : ℝ => |lam (Real.exp (y + Real.log z))|) volume := by
    have hmp : MeasureTheory.MeasurePreserving (fun y : ℝ => y + Real.log z) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (Real.log z)
    have hemb : MeasurableEmbedding (fun y : ℝ => y + Real.log z) :=
      measurableEmbedding_addRight (Real.log z)
    exact ((hmp.integrable_comp_emb hemb).mpr hint).abs
  -- (2) reflect the line, `x ↦ -x`, which is the dilation by `-1` (a nonzero scalar)
  have h2 : MeasureTheory.Integrable
      (fun x : ℝ => |lam (Real.exp ((-1 : ℝ) * x + Real.log z))|) volume :=
    h1.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  -- (3) identify the two arguments: `exp ((-1) * x + log z) = z * exp (-x)`
  have hfun : ∀ x : ℝ, Real.exp ((-1 : ℝ) * x + Real.log z) = z * Real.exp (-x) := by
    intro x
    rw [show (-1 : ℝ) * x + Real.log z = Real.log z - x by ring, Real.exp_sub,
      Real.exp_log hz, div_eq_mul_inv, Real.exp_neg]
  have h3 : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-x))|) volume :=
    h2.congr (Filter.Eventually.of_forall fun x => congrArg (fun t => |lam t|) (hfun x))
  exact h3.integrableOn

end Work.FTS.StrongEps.EpsLocalPStar
