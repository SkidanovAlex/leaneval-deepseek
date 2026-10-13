import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.StepFacts.Jker_moment_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.GainDens

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `Jker_lintegral_mul_exp_lt_top`.
The `δ`-moment of the rescaled kernel is finite: immediate from `StepFacts.Jker_moment_le`
(integrability of `p ↦ Jker σ ε p * exp (δ|p|)`), turned into the `lintegral` of `ofReal` via
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (the integrand is nonnegative because `hσ0`
makes `Jker σ ε ≥ 0`). -/
theorem Jker_lintegral_mul_exp_lt_top {σ : ℝ × ℝ → ℝ} (hσ0 : ∀ q : ℝ × ℝ, 0 ≤ σ q)
    (hσc : Continuous σ) (hσs : ∀ q : ℝ × ℝ, σ q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p
        * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ := by
  -- `Jker σ ε` is nonnegative, hence so is the whole integrand
  have hker_nonneg : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker σ ε p := by
    intro p
    have h := hσ0 (ε⁻¹ • p)
    rw [Work.FTS.StrongEps.Jker]
    nlinarith [sq_nonneg (ε⁻¹ : ℝ)]
  have hnonneg : ∀ p : ℝ × ℝ,
      0 ≤ Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|)) :=
    fun p => mul_nonneg (hker_nonneg p) (Real.exp_nonneg _)
  -- integrability of the `δ`-moment, from `Jker_moment_le` with `γ = δ`
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|))) :=
    (Work.FTS.StrongEps.StepFacts.Jker_moment_le σ hσ0 hσc hσs hε hε1 hδ).1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall hnonneg)]
  exact ENNReal.ofReal_lt_top

end Work.FTS.StrongEps.EpsE4Thr.GainDens
