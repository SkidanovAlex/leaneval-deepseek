import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- One-dimensional Cauchy–Schwarz with an *unconditional* integrability convention: if `A, B`
are nonnegative a.e. and in `L²(μ)`, and `|g| ≤ A·B` a.e., then
`|∫ g dμ| ≤ √(∫A²) √(∫B²)`.  No measurability or integrability of `g` is assumed; when `|g|`
fails to be integrable, `∫ |g|` is `0` by the junk-value convention
(`MeasureTheory.integral_undef`, via `MeasureTheory.abs_integral_le_integral_abs`) and the
inequality holds trivially.

Intended proof: `|∫ g| ≤ ∫ |g| ≤ ∫ A·B` (the second step is `MeasureTheory.integral_mono_ae`
in the case `MeasureTheory.Integrable |g| μ`, and `MeasureTheory.integral_undef` otherwise),
then Cauchy–Schwarz in squared form (`Real.holderConjugate_iff` with `p = q = 2` and
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`; `Work.Spaces.cs_integral` in
`Submission.Work.Spaces.cs_integral` is the same statement for `μ = volume.restrict s` with
`MemLp` hypotheses) to get `(∫ A·B)² ≤ (∫A²)(∫B²)`, and finally
`∫A·B = √((∫A·B)²) ≤ √(∫A²)√(∫B²)` because `A·B ≥ 0` a.e. -/
theorem CS1D {μ : MeasureTheory.Measure ℝ} {g A B : ℝ → ℝ}
    (hA : MeasureTheory.MemLp A 2 μ) (hB : MeasureTheory.MemLp B 2 μ)
    (hA0 : 0 ≤ᵐ[μ] A) (hB0 : 0 ≤ᵐ[μ] B)
    (hg : ∀ᵐ r ∂μ, |g r| ≤ A r * B r) :
    |∫ r, g r ∂μ| ≤ Real.sqrt (∫ r, A r ^ 2 ∂μ) * Real.sqrt (∫ r, B r ^ 2 ∂μ) := by
  -- `A · B` is integrable, being the product of two `L²` functions.
  have hAB : MeasureTheory.Integrable (fun r => A r * B r) μ := hA.integrable_mul hB
  -- Step 1: `|∫ g| ≤ ∫ |g| ≤ ∫ A·B`.  `MeasureTheory.norm_integral_le_of_norm_le` bundles
  -- the two inequalities and — crucially — needs *no* hypothesis on `g` itself.
  have h1 : |∫ r, g r ∂μ| ≤ ∫ r, A r * B r ∂μ := by
    refine MeasureTheory.norm_integral_le_of_norm_le (f := g) hAB ?_
    filter_upwards [hg] with r hr
    rwa [Real.norm_eq_abs]
  -- Step 2: Hölder with conjugate exponents `p = q = 2`.
  have h2 : ∫ r, A r * B r ∂μ
      ≤ (∫ r, A r ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫ r, B r ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    have hA2 : MeasureTheory.MemLp A (ENNReal.ofReal 2) μ := by simpa using hA
    have hB2 : MeasureTheory.MemLp B (ENNReal.ofReal 2) μ := by simpa using hB
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hA0 hB0 hA2 hB2
  -- The `ℝ`-powers of exponent `2` are the integer powers.
  have h3 : (∫ r, A r ^ (2 : ℝ) ∂μ) = ∫ r, A r ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun r => Real.rpow_natCast (A r) 2)
  have h4 : (∫ r, B r ^ (2 : ℝ) ∂μ) = ∫ r, B r ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun r => Real.rpow_natCast (B r) 2)
  calc |∫ r, g r ∂μ| ≤ ∫ r, A r * B r ∂μ := h1
    _ ≤ (∫ r, A r ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
          * (∫ r, B r ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := h2
    _ = Real.sqrt (∫ r, A r ^ 2 ∂μ) * Real.sqrt (∫ r, B r ^ 2 ∂μ) := by
        rw [h3, h4, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end Work.FTS.H2
