/-
# The `L²`-endgame on a general polydisc, in a solver-chain-compatible import closure

`Work.NN.Final.eLpNorm_le_of_holderNorm_zero` (`l2ExistenceDefs.lean`) is the case `σ = 2`.
`Work.NN.Final.eLpNorm_le_of_holderNorm_zero_pd` (`uniformDbarL2_holds.lean`) is the general case,
but that file's import closure contains the `exists_holderNorm_wirtinger_le` chain, which is
*incompatible* with the `Ratio`/`recU` solver chain (duplicate `Work.NN.Core.holderNorm_congr`; see
`NOTES_uniformDbarL2_session.md` §10).  This file re-proves the same statement importing only the two
modules needed, so that it can be combined with `Submission.Work.NN.Final.dbar_open_ratio_local`.
-/
import Mathlib
import Submission.Work.NN.Core.eLpNorm_le_iterDerivNorm_zero
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.CR.Flat

namespace Work.NN.Final

/-- **`L²` is controlled by the `C^{0,α}`-norm on `pd n ρ σ`.**  For every `σ > 0` and positive
radii `ρ` there is `K > 0` with
`eLpNorm u 2 (volume.restrict (pd n ρ σ)) ≤ K · holderNorm 0 α u (pd n ρ σ)`
for every a.e. strongly measurable `u`.  (Take `K = (volume (pd n ρ σ))^{1/2} + 1`; the sup-norm part
of the `C^{0,α}`-norm controls the pointwise norm.) -/
theorem eLpNorm_le_holderNorm_zero_pd {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : Work.NN.Core.Cn n → ℂ), AEStronglyMeasurable u (volume.restrict (pd n ρ σ)) →
        ∀ (M : ℝ≥0∞), holderNorm 0 α u (pd n ρ σ) ≤ M →
          eLpNorm u 2 (volume.restrict (pd n ρ σ)) ≤ ENNReal.ofReal K * M := by
  have hσρ : ∀ j, 0 < σ * ρ j := fun j => mul_pos hσ (hρ j)
  obtain ⟨V, hVpos, hV⟩ :=
    Work.NN.Core.eLpNorm_le_iterDerivNorm_zero (n := n) (ρ := fun j => σ * ρ j) hσρ
  refine ⟨V, hVpos, fun u hu M hM => ?_⟩
  have hpd : pd n ρ σ = polydisc 0 (fun j => σ * ρ j) := rfl
  rw [hpd] at hu hM ⊢
  refine le_trans (hV u hu) ?_
  calc ENNReal.ofReal V * iterDerivNorm 0 u (polydisc 0 (fun j => σ * ρ j))
      ≤ ENNReal.ofReal V * holderNorm 0 α u (polydisc 0 (fun j => σ * ρ j)) := by
        gcongr
        exact iterDerivNorm_le_holderNorm 0 α u _ le_rfl
    _ ≤ ENNReal.ofReal V * M := by gcongr

end Work.NN.Final
