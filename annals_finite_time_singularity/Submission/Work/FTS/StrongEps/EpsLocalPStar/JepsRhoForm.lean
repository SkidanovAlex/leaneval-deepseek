/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsLocalPStar/JepsRhoForm` — `Jeps` in the *unshifted* kernel variable

`Jeps ρ ε` is defined (`StrongEps/Basic.lean`) as the integral of the rescaled kernel
`Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)` against the shifts `z ↦ z e^{-p₁}`,
`θ ↦ arctan (tan θ e^{-p₂})`:

  `Jeps ρ ε f z θ = ∫ p, ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) * f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`.

This file records the equivalent form in which the *kernel* carries no scaling factor, i.e. the
change of variables `p ↦ ε • p` in the two-dimensional `p`-integral:

  `Jeps ρ ε f z θ = ∫ q, ρ q * f (z e^{-ε q₁}) (arctan (tan θ e^{-ε q₂}))`.

The substitution is the additive-Haar-measure scaling `∫ p, g (ε • p) = ε² • ∫ q, g q`
(`Measure.integral_comp_inv_smul_of_nonneg`), which Mathlib states for *arbitrary* integrands
(both sides then agree by the Bochner convention that a non-integrable function has integral
`0`).  Consequently the identity below carries no measurability or integrability hypothesis
whatsoever; in particular it holds for a merely continuous mollifier `ρ`.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory

/-- **The scaling substitution behind `Jker`.**  For every `h : ℝ × ℝ → ℝ` (no measurability or
integrability hypothesis: both sides use the Bochner convention `integral_undef`),

  `∫ p, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p = ∫ q, ρ q * h (ε • q)`,

i.e. the rescaled kernel can be traded for the plain kernel at the price of evaluating the
integrand at the scaled point `ε • q`. -/
theorem integral_inv_smul_mollify (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (h : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p)
      = ∫ q : ℝ × ℝ, ρ q * h (ε • q) := by
  -- the two-dimensional Haar scaling `∫ p, F (ε⁻¹ • p) = (ε⁻¹)² • ∫ p, F p`
  have hkey := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (ℝ × ℝ))) (fun u : ℝ × ℝ => ρ u * h (ε • u)) (R := ε) hε.le
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod]] at hkey
  -- `ε⁻¹ • (ε • x) = x`, so the left-hand side is the integral of `ρ (ε⁻¹ • x) * h x`
  have hleft : (∫ x : ℝ × ℝ, (fun u : ℝ × ℝ => ρ u * h (ε • u)) (ε⁻¹ • x))
      = ∫ x : ℝ × ℝ, ρ (ε⁻¹ • x) * h x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ρ (ε⁻¹ • x) * h (ε • (ε⁻¹ • x)) = ρ (ε⁻¹ • x) * h x
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  rw [hleft, smul_eq_mul] at hkey
  calc (∫ p : ℝ × ℝ, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p)
      = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) * h p := by
        rw [← MeasureTheory.integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ q : ℝ × ℝ, ρ q * h (ε • q)) := by rw [hkey]
    _ = ∫ q : ℝ × ℝ, ρ q * h (ε • q) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]

/-- **`Jeps` with the unshifted kernel.**  On the open quadrant the mollifier equals the
`ρ`-average of the profile along the *scaled* shifts `z e^{-ε q₁}`, `arctan (tan θ e^{-ε q₂})`:
the factor `ε⁻¹ ^ 2` of `Jker` is exactly the Jacobian of `p = ε q`. -/
theorem JepsRhoForm (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hε : 0 < ε) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε f z θ
      = ∫ q : ℝ × ℝ, ρ q * f (z * Real.exp (-(ε * q.1)))
          (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2)))) := by
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hz hθ]
  simp only [Work.FTS.StrongEps.Jker, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
  have hmain := integral_inv_smul_mollify ρ hε
    (fun u : ℝ × ℝ => f (z * Real.exp (-u.1)) (Real.arctan (Real.tan θ * Real.exp (-u.2))))
  rw [hmain]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

end Work.FTS.StrongEps.EpsLocalPStar
