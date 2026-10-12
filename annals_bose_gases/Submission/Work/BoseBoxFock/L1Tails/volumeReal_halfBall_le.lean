import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.chiBasicFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.volumeReal_halfBall_le`

The volume of the `ℓ`-half-ball `halfBall ℓ = closedBall 0 (ℓ/2)` of `ℝ³` is at most `ℓ³`.

This is the elementary constant used whenever the `y`-integral of `ψ_m` is estimated by
Cauchy–Schwarz against the constant function on the half-ball (see
`Work.BoseBoxFock.L1Tails.sq_setIntegral_halfBall_le`).

The proof is by containment: `halfBall ℓ ⊆ boxL ℓ` (the corpus box, of volume exactly `ℓ³`),
which is `chiBasicFacts.halfBall_subset_boxL`.
-/

open MeasureTheory
open scoped Topology

namespace Work.BoseBoxFock.L1Tails

theorem volumeReal_halfBall_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
      (Work.BoseBoxFock.L1Tails.halfBall ℓ) ≤ ℓ ^ 3 := by
  have hsub : halfBall ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := halfBall_subset_boxL hℓ
  have hnt : (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
    exact ENNReal.ofReal_ne_top
  have h1 := measureReal_mono hsub hnt
  have h2 : (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
      (Work.BoseK15.corpusBox.boxL ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
      ENNReal.toReal_ofReal (by positivity)]
  linarith

end Work.BoseBoxFock.L1Tails
