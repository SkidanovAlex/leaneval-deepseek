import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.slotSplit_pDiagForm_smooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for the faithful (`pDiagForm`) small-box kinetic word

The requested theorem `Work.KinPSuperadd.slotSplit_pDiagForm` is the block
decomposition of the sum-of-one-particle-forms word
`K N Φ = pDiagForm s F N Φ`.

**The hypothesis is the smooth one.**  In the statement below the smoothness
degree is written `↑(⊤ : ℕ∞)`, which is exactly the `ContDiff`-scoped notation
`∞` (`scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)`): the coercion
`↑ : ℕ∞ → WithTop ℕ∞` is `WithTop.some`, so `↑(⊤ : ℕ∞) = ∞` is the top *finite*
surrogate in `WithTop ℕ∞`, i.e. `C^∞`, and NOT the outer top `⊤ : WithTop ℕ∞`
(which is `C^ω` = analytic, `contDiff_omega_iff_analyticOnNhd`).  Indeed
`ContDiff ℝ (↑(⊤ : ℕ∞))` and `ContDiff ℝ ∞` are the same term, so the hypothesis
`hint` requested here is *identical* to the one of
`Work.KinPSuperadd.slotSplit_pDiagForm_smooth`, whose proof (sorry-free, in
`slotSplit_pDiagForm_smooth.lean`) already establishes the statement for
arbitrary `F ≥ 0` and box side `s`.  The theorem below is therefore the same
statement, transported.

(For `s ≤ 0` every box with `N ≠ 0` is null and `(s³)⁻¹ = 0`, so `pDiagForm`
vanishes; for `s > 0` the block identity is `Σ_i` of the per-slot Fubini
identities, which is what the referenced module proves.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem slotSplit_pDiagForm (s : ℝ) (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) Ψ →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        F ‖p‖ * ∑ i : Fin N, (s ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox N s,
            ‖Submission.BoseGases.pSlotAmp s p Ψ i x‖ ^ 2)) :
    @Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
        => @Submission.BoseGases.pDiagForm s F N Φ) :=
  slotSplit_pDiagForm_smooth s F hF hint

end Work.KinPSuperadd
