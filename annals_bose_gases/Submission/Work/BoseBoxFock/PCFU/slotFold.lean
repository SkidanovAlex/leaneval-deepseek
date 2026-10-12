import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.kernelTail
import Submission.Work.BoseBoxFock.PCFU.latPerCWeightIntegral
import Submission.Work.BoseBoxFock.PCFU.psiLatPer3Integrable
import Submission.Work.BoseBoxFock.PCFU.slotPeriodisationReduction
import Submission.Work.BoseBoxFock.latPer_bdd_global
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.slotFold` — the periodisation/dual-lattice pairing formula

For an even `L¹` weight `W` supported in the ball of radius `R` and a smooth compactly supported
`Ψ`, the pairing of `Ψ` with the `ℓℤ³`-periodisation `latPer3 ℓ W = ℓ³ Σ'_m W(· + ℓ • latVec m)`
equals the lattice sum of the products of the `p`-convention Fourier samples on the dual lattice
`κ_n = (2π/ℓ) • n`:

  `∫ Ψ (latPer3 ℓ W) = Σ'_n kinFT W (κ_n) · kinFT Ψ (-κ_n)`.

Route (Poisson/Parseval on the cell, in the shape used by the `L¹Tails` chapter):

* `psiLatPer3Integrable` — the left side is an honest integral (a finite sum on `supp Ψ`);
* `slotPeriodisationReduction` — folding: `∫ Ψ · latPer3 ℓ W = ℓ³ ∫ W · latPerC ℓ Ψ`;
* `latPerCWeightIntegral` — the `ℂ`-valued periodisation `latPerC ℓ Ψ` has the absolutely and
  uniformly convergent lattice Fourier series `Σ'_n (ℓ³)⁻¹ Ŵ(κ_n) e^{i⟪κ_n,z⟫}`
  (`Work.BoseBoxFock.L1Tails.latPerC_hasSum_fourier`), whose termwise integration against the
  `L¹` weight `W` gives the lattice sum;
* the character integral `∫ W (e^{i⟪κ_n,·⟫})` is `kinFT W (-κ_n)` (an `n ↦ -n` reindexing and the
  scalar cancellation `ℓ³ · (ℓ³)⁻¹ = 1` finish the bookkeeping).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

theorem slotFold {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWev : ∀ x, W (-x) = W x) (hWs : ∀ x, R ≤ ‖x‖ → W x = 0)
    {Ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨs : HasCompactSupport Ψ) :
    MeasureTheory.Integrable (fun z => Ψ z * Work.BoseBoxFock.latPer3 ℓ W z)
      ∧ (∫ z, Ψ z * Work.BoseBoxFock.latPer3 ℓ W z
        = ∑' n : Fin 3 → ℤ,
            Submission.BoseGases.kinFT (fun v => ((W v : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)
              * Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))) := by
  refine ⟨psiLatPer3Integrable hℓ hW hWs hΨ hΨs, ?_⟩
  have hWcint : MeasureTheory.Integrable (fun v : E3 => ((W v : ℝ) : ℂ)) := hW.ofReal
  rw [slotPeriodisationReduction (ℓ := ℓ) (R := R) hℓ hW hWs hΨ hΨs,
    latPerCWeightIntegral (ℓ := ℓ) hℓ hWcint hΨ hΨs]
  -- (i) the character integral is the reflected Fourier sample of the weight
  have hstep4 : ∀ n : Fin 3 → ℤ,
      (∫ z : E3, ((W z : ℝ) : ℂ) * Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
        = Submission.BoseGases.kinFT (fun v : E3 => ((W v : ℝ) : ℂ))
            (-(Work.BoseBoxFock.kappaL ℓ n)) := by
    intro n
    show (∫ z : E3, ((W z : ℝ) : ℂ) * Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
        = ∫ y : E3, Complex.exp (-(Complex.I *
            ((inner ℝ (-(Work.BoseBoxFock.kappaL ℓ n)) y : ℝ) : ℂ))) * ((W y : ℝ) : ℂ)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    have hexp : Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))
        = Complex.exp (-(Complex.I *
          ((inner ℝ (-(Work.BoseBoxFock.kappaL ℓ n)) z : ℝ) : ℂ))) := by
      congr 1
      rw [inner_neg_left]
      push_cast
      ring
    rw [mul_comm (((W z : ℝ) : ℂ)), hexp]
  -- (ii) the scalar algebra `ℓ³ * (c * ((ℓ³)⁻¹ * d)) = c * d`
  have hscal : ∀ c d : ℂ,
      ((ℓ ^ 3 : ℝ) : ℂ) * (c * ((((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) * d)) = c * d := by
    intro c d
    have h2 : ((ℓ ^ 3 : ℝ) : ℂ) ≠ 0 := by
      push_cast
      exact pow_ne_zero 3 (by exact_mod_cast ne_of_gt hℓ)
    rw [Complex.ofReal_inv]
    field_simp
    try ring_nf
  -- (iii) reindex the target sum by `n ↦ -n`
  rw [← tsum_comp_neg (fun n : Fin 3 → ℤ =>
      Submission.BoseGases.kinFT (fun v : E3 => ((W v : ℝ) : ℂ))
          (Work.BoseBoxFock.kappaL ℓ n)
        * Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n)))]
  -- (iv) push `ℓ³` inside the sum and compare termwise
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Work.BoseBoxFock.L1Tails.kappaL_neg, neg_neg, hstep4 n]
  exact hscal _ _

end Work.BoseBoxFock.PCFU
