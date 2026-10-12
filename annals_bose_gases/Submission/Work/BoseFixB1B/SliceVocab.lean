import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxCountGeB1
import Submission.Work.BoseFixB1S.boxQmassNeutralB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.SliceVocab` — the import point of the FS-Step-E (grouping) vocabulary

The **grouping** (FS Step E, `final_v2.tex` 3960–4045) at the *sliding* box needs, in one place:
`Submission.BoseGases.qLHSword`/`qLHSden` and the block-split lemmas of
`Submission.Work.SmallBoxSuperadd`, the restricted Fubinis of `Submission.Work.AboxBlockSplit`,
the box projections `boxPInd`/`boxQInd` and the words `cnPlusBoxInd`/`tBdiagFormInd`/`tBwordKinInd`
of `Submission.Work.UBBInputs8`, the sliding word `sbKin`/`sbPot`/`sbWord` of
`Submission.Work.BoseFixB1.Defs`, and the count vocabulary `boxFlatCount`/`boxQCount`/… of
`Submission.Work.BoseFixB1S.BoxQWords`.

This module is *only* an import point (no mathematics): it exists so that the lemmas of this
chapter (`Submission/Work/BoseFixB1B/SliceSuperadd.lean`, …) and the delegated rungs that prove
them share one vocabulary module.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The restricted Fubini identity of `Submission.Work.AboxBlockSplit`, restated with the sliding
box side `ℓ` (a definitional alias, so that the delegated rungs can cite a name in this
namespace). -/
theorem aboxFubini_slice {N1 N2 : ℕ} (ℓ : ℝ) (G : Submission.BoseGases.X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (Submission.BoseGases.abox (N1 + N2) ℓ) volume) :
    (∫ u in Submission.BoseGases.abox N1 ℓ,
        ∫ w in Submission.BoseGases.abox N2 ℓ, G (Submission.BoseGases.mergeBlock N1 N2 (u, w)))
      = ∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, G x :=
  Submission.BoseGases.aboxFubini ℓ G hG

/-- The `w`-outer restricted Fubini identity, with the sliding box side `ℓ`. -/
theorem aboxFubini_slice_swapped {N1 N2 : ℕ} (ℓ : ℝ)
    (G : Submission.BoseGases.X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (Submission.BoseGases.abox (N1 + N2) ℓ) volume) :
    (∫ w in Submission.BoseGases.abox N2 ℓ,
        ∫ u in Submission.BoseGases.abox N1 ℓ, G (Submission.BoseGases.mergeBlock N1 N2 (u, w)))
      = ∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, G x :=
  Submission.BoseGases.aboxFubini_swapped ℓ G hG

end Work.BoseFixB1B
