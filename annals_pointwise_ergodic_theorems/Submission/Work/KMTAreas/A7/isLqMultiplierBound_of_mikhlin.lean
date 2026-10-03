import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal

/-- The Mikhlin multiplier theorem, in the shape of the paper's Appendix `iw-app`: a symbol
satisfying the Mikhlin conditions with constant `A` defines a bounded Fourier multiplier on
`L^q(ℝ)` with norm at most `C_q A`, and the same holds for the conjugate symbol
`x ↦ star (ψ x)` (the adjoint multiplier, needed for the dual exponents).

The bound for `ψ` is `Commons.Analysis.Fourier.mikhlin_multiplier_lp`, converted from the explicit
integral form of `contMulOp` to the `eLpNorm` form `IsLqMultiplierBound`, and the bound for the
conjugate symbol is `Work.KMTAreas.A7.IsLqMultiplierBound_star`. -/
theorem isLqMultiplierBound_of_mikhlin (q : ℝ) (hq : 1 < q) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ {ψ : ℝ → ℂ} {A : ℝ} (hψcd : ContDiff ℝ 2 ψ),
      Work.KMTAreas.A7.MikhlinBound ψ A →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q) ψ
        (Real.toNNReal (Cq * A)) ∧
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q) (fun x : ℝ => star (ψ x))
        (Real.toNNReal (Cq * A)) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp q hq
  refine ⟨Cm, hCmpos, ?_⟩
  intro ψ A hψcd hA
  have hA0 : 0 ≤ A := hA.1
  have hCA : 0 ≤ Cm * A := mul_nonneg hCmpos.le hA0
  have hmul : ENNReal.ofReal (Cm * A)
      = ENNReal.ofReal ((Real.toNNReal (Cm * A) : NNReal) : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_eq_coe_nnreal hCA,
      Real.toNNReal_of_nonneg hCA]
  have hmain : Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q) ψ
      (Real.toNNReal (Cm * A)) := by
    intro G
    have hG := hCm ψ A hA0 hψcd hA.2.1 hA.2.2.1 hA.2.2.2 G
    have hcongr : Work.Analysis.IWMultiplier.contMulOp ψ (G : ℝ → ℂ)
        = fun x : ℝ => ∫ ξ : ℝ,
            (ψ ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
              • (FourierTransform.fourier (G : ℝ → ℂ) ξ) := by
      funext x
      exact contMulOp_eq_integral ψ G x
    rw [hcongr]
    refine le_trans hG ?_
    rw [← hmul]
  exact ⟨hmain, IsLqMultiplierBound_star hmain⟩

end Work.KMTAreas.A7
