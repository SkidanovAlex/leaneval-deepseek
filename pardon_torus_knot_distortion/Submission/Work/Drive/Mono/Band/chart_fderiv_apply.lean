import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs

namespace Work.Drive.Mono.Band

/-- **The derivative of the projective chart of the Gauss normal.**  If the `b₀`-component
`betaV ψ v b₀ p` of the projected Gauss normal does not vanish at `p`, then the quotient
`alphaV ψ v a₀ / betaV ψ v b₀` has, in the direction `w`, the derivative given by the quotient rule.
Route: write the quotient as `alphaV * (betaV)⁻¹` (`div_eq_mul_inv`), use `fderiv_mul`, the chain
rule and `hasFDerivAt_inv` (or `fderiv_inv`) applied to `betaV`, with differentiability of
`alphaV`, `betaV` from `contDiff_alphaV` / `contDiff_betaV` of `BandChartDefs`.
(Namespace `Work.Drive.Mono.Band`.) -/
theorem chart_fderiv_apply (ψ : Submission.Diffeo)
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) {p : ℝ × ℝ}
    (hβ : Work.Drive.Mono.Band.betaV ψ v b₀ p ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ =>
        Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q) p w
      = (fderiv ℝ (Work.Drive.Mono.Band.alphaV ψ v a₀) p w * Work.Drive.Mono.Band.betaV ψ v b₀ p
          - Work.Drive.Mono.Band.alphaV ψ v a₀ p
            * fderiv ℝ (Work.Drive.Mono.Band.betaV ψ v b₀) p w)
        / (Work.Drive.Mono.Band.betaV ψ v b₀ p)^2 := by
  have hα : DifferentiableAt ℝ (alphaV ψ v a₀) p :=
    ((contDiff_alphaV ψ v a₀).differentiable (by norm_num)) p
  have hβd : DifferentiableAt ℝ (betaV ψ v b₀) p :=
    ((contDiff_betaV ψ v b₀).differentiable (by norm_num)) p
  have hβinv : DifferentiableAt ℝ (fun q : ℝ × ℝ => (betaV ψ v b₀ q)⁻¹) p := hβd.inv hβ
  simp only [div_eq_mul_inv]
  have hprod : fderiv ℝ (fun q : ℝ × ℝ => alphaV ψ v a₀ q * (betaV ψ v b₀ q)⁻¹) p w
      = alphaV ψ v a₀ p * (fderiv ℝ (fun q : ℝ × ℝ => (betaV ψ v b₀ q)⁻¹) p w)
        + (betaV ψ v b₀ p)⁻¹ * (fderiv ℝ (alphaV ψ v a₀) p w) := by
    rw [show (fun q : ℝ × ℝ => alphaV ψ v a₀ q * (betaV ψ v b₀ q)⁻¹)
        = (alphaV ψ v a₀) * (fun q : ℝ × ℝ => (betaV ψ v b₀ q)⁻¹) from rfl,
      fderiv_mul hα hβinv]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hprod]
  have hfinv : fderiv ℝ (fun q : ℝ × ℝ => (betaV ψ v b₀ q)⁻¹) p
      = (ContinuousLinearMap.toSpanSingleton ℝ (-(betaV ψ v b₀ p ^ 2)⁻¹)).comp
          (fderiv ℝ (betaV ψ v b₀) p) := by
    change fderiv ℝ ((fun x : ℝ => x⁻¹) ∘ (betaV ψ v b₀)) p = _
    rw [(HasFDerivAt.comp p (hasFDerivAt_inv hβ) hβd.hasFDerivAt).fderiv]
  rw [hfinv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  field_simp
  ring

end Work.Drive.Mono.Band
