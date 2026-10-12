import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.fsT_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.fsT_nonneg_of_continuous` — `𝒯_u` is nonnegative for *continuous* `ψ`

`Work.BoseKinLoc.Word.fsT_nonneg` proves `0 ≤ fsT ℓ d s εT b u ψ` under the hypotheses
`ψ ∈ C^∞` and `HasCompactSupport ψ`.  Neither is needed: the only place where any regularity
of `ψ` enters is the integrability of `(Q_uψ)²` over the moving box `Λ(u)`, and `Λ(u)` lies in
a *compact* closed ball (`NeuFrac.lamBox_subset_closedBall`), so plain continuity of `ψ`
suffices — `Q_uψ = ψ − (box mean of ψ)` is then continuous, hence square integrable on `Λ(u)`.
The remaining three words of FS `eq:DefT` (`gapWord`, `momWord`, `mainWord`) are nonnegative
with no regularity hypothesis at all.

This is exactly the hypothesis regime needed by the applications where `ψ` is a fibre
`z ↦ Φ(x with xᵢ = z)` of a merely continuous `N`-body state.

## Contents

* `fsT_nonneg_of_continuous` — the requested statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Word

set_option linter.unusedVariables false

/-- **The localised kinetic word `𝒯_u` of FS `eq:DefT` is nonnegative for a continuous
one-body state.**

`fsT ℓ d s εT b u ψ` is the sum of the four pieces of FS `eq:DefT`, each of which is
nonnegative: the Neumann-resolvent word `neuWord` because the box Neumann fraction `neuFrac`
of the mean-free state `Q_uψ` is nonnegative (`neuFrac_nonneg_of_integrableSq`, whose only
input is the square-integrability of `Q_uψ` on the compact box `Λ(u)` — supplied here by
continuity of `ψ`), and `gapWord`, `momWord`, `mainWord` by
`Defs.gapWord_nonneg`, `Defs.momWord_nonneg`, `Defs.mainWord_nonneg`. -/
theorem fsT_nonneg_of_continuous {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    0 ≤ Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  -- `Q_uψ = ψ − (box mean of ψ)` is continuous, hence square integrable on the box `Λ(u)`
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.sub continuous_const
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
      (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)
  -- the four words
  have hneu : 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
    have hn := neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 u hI
    unfold Work.BoseKinLoc.neuWord
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT) ha2) hn
  have hgap : 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ :=
    Work.BoseKinLoc.gapWord_nonneg hb hℓ.le u ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ :=
    Work.BoseKinLoc.momWord_nonneg hb hεT hdℓ.le u ψ
  have hmain : 0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    Work.BoseKinLoc.mainWord_nonneg hεT hεT1 u ψ
  rw [Work.BoseKinLoc.fsT_eq_sum]
  linarith

end Work.BoseKinLoc.Word
