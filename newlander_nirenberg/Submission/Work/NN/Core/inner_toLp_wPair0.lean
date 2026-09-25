import Mathlib
import Submission.Work.NN.Core.PertL2Defs
import Submission.Work.NN.Assemble.pertDefs

open MeasureTheory
open scoped NNReal ENNReal

namespace Work.NN.Core

/-- The `L²` inner product `⟪u, g⟫_{L²(wMeas)}` of an `L²`-class `u` with the class of a
function `g` (in the weighted measure `wMeas n φ = e^{-φ} dz`) is the weighted pairing
`wPair0 φ g u = ∫ g · conj u · e^{-φ} dz` of `g` with the representative `⇑u`.

The proof is the definition of the `L²` inner product (`MeasureTheory.L2.inner_def`, so
`⟪u, w⟫ = ∫ ⟪u z, w z⟫ ∂(wMeas n φ)`), the `L²`-convention `⟪a, b⟫_ℂ = b · conj a`, the fact that
`MemLp.toLp g hg` agrees with `g` almost everywhere, and the change of measure
`∫ F ∂(volume.withDensity ρ) = ∫ F · ρ ∂volume` for the density `ρ = e^{-φ}`. -/
theorem inner_toLp_wPair0 {n : ℕ} {φ : Work.NN.Assemble.Cn n → ℝ} (hφ : Measurable φ)
    {g : Work.NN.Assemble.Cn n → ℂ} (hg : MeasureTheory.MemLp g 2 (Work.NN.Core.wMeas n φ))
    (u : MeasureTheory.Lp ℂ 2 (Work.NN.Core.wMeas n φ)) :
    inner ℂ u (MeasureTheory.MemLp.toLp g hg)
      = Work.NN.Assemble.wPair0 φ g (⇑u) := by
  rw [MeasureTheory.L2.inner_def]
  -- Replace the chosen representative of the class of `g` by `g` itself.
  have hcoe : (fun z : Work.NN.Assemble.Cn n =>
        inner ℂ ((u : Work.NN.Assemble.Cn n → ℂ) z)
          ((MeasureTheory.MemLp.toLp g hg : Work.NN.Assemble.Cn n → ℂ) z))
      =ᵐ[Work.NN.Core.wMeas n φ]
      (fun z : Work.NN.Assemble.Cn n =>
        inner ℂ ((u : Work.NN.Assemble.Cn n → ℂ) z) (g z)) :=
    hg.coeFn_toLp.mono (fun z hz => by simp only [hz])
  rw [integral_congr_ae hcoe]
  rw [Work.NN.Assemble.wPair0]
  -- Unfold the weighted measure, so that the change-of-density lemma applies syntactically.
  show (∫ z, inner ℂ ((u : Work.NN.Assemble.Cn n → ℂ) z) (g z)
          ∂(volume.withDensity (fun z => ((Real.exp (-(φ z))).toNNReal : ℝ≥0∞))))
      = ∫ z, g z * star ((u : Work.NN.Assemble.Cn n → ℂ) z) * (Real.exp (-(φ z)) : ℂ)
  rw [integral_withDensity_eq_integral_smul₀
    (f := fun z => (Real.exp (-(φ z))).toNNReal)
    (Measurable.real_toNNReal (Real.measurable_exp.comp hφ.neg)).aemeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [RCLike.inner_apply, starRingEnd_apply, NNReal.smul_def]
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]
  ring

end Work.NN.Core
