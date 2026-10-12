import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxFlatSqJensen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.flatArm37LowerAux` — the **holder-free** extraction of
# `Work.BoseB1Cube.pairCountPayment`

## BRIEF for the prover of `Work.BoseB1Cube.flatArm37RowOneGoodLower`

The statement of `flatArm37RowOneGoodLower` is a **verbatim copy** (same hypotheses, same
conclusion, only the name changed) of the PROVED theorem

    Work.BoseB1Cube.flatArm37RowOneGood        (`Submission/Work/BoseB1Cube/flatArm37RowOneGood.lean:300`)

whose file contains the whole proof, `sorry`-free and axiom-clean.  **Do not re-derive the
mathematics**: copy that file's body.  The *only* reason that file cannot be used as-is is its
**import cone**: it imports `Submission.Work.BoseB1Cube.cubeFlatArm_holds`, whose cone contains
`… → nominalPerBoxRow → nomRowSqWindowRow → cubeSmallNArb12ExHolds` — the *holder* of the parent
node (and `rowsOfSmallWindow.olean` is currently absent, so nothing in that cone even builds).
A module the holder itself must import can never be in that cone.

`flatArm37RowOneGood.lean` uses **exactly one** declaration from the forbidden file
`cubeFlatArm_holds` — the 25-line `Work.BoseB1Cube.pairCountPayment` (at
`cubeFlatArm_holds.lean:87`), which is a direct corollary of the PROVED
`Work.BoseFixB1S.boxFlatSqJensen`.  It is re-supplied here under the new name
**`Work.BoseB1Cube.pairCountPaymentLower`**, so that the copy only has to
replace `pairCountPayment` by `pairCountPaymentLower` and drop the import of `cubeFlatArm_holds`.

### Suggested recipe (mechanical)

1. Copy `Submission/Work/BoseB1Cube/flatArm37RowOneGood.lean` into
   `Submission/Work/BoseB1Cube/flatArm37RowOneGoodLower.lean`.
2. Import list: keep every import of the original **except**
   `Submission.Work.BoseB1Cube.cubeFlatArm_holds`; do **not** add `cubeFlatArm_holds`,
   `cubeSmallWinFlatArm37`, `flatArm37RowOneGood`, `rowsOfSmallWindow`, `cubeSmallNArb12ExHolds`,
   or anything importing them.  Add `Submission.Work.BoseB1Cube.flatArm37LowerAux`.
3. Replace the single use of `Work.BoseB1Cube.pairCountPayment` (in the proof of `rowOneMain`'s
   caller, the `hpairPay` step) by `Work.BoseB1Cube.pairCountPaymentLower`.
4. Rename the main theorem `flatArm37RowOneGood` ↦ `flatArm37RowOneGoodLower` (the statement must be
   **byte-identical** otherwise).  The four helper lemmas `sqrt_mul_le_add_div`,
   `boxM1_eq_w1MassB`, `boxM2_g2_le_v_box`, `w1MassB_le_boxM2_v`, `rowOneLedger`, `rowOneFinal`,
   `rowOneMain` may keep their names, but mark them **`private`** (they are re-declared by
   `flatArm37RowOneGood.lean`, and the two files must be importable together by later modules).
   `private` affects neither the statement nor `#print axioms` of the main theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The pair payment of the flat count, holder-free copy.**  Dividing the PROVED
`Work.BoseFixB1S.boxFlatSqJensen` (`S² − S·N ≤ N·boxPairCount`) by `N = ‖Φ‖² > 0` gives
`S²/N − S ≤ boxPairCount`.  This is a verbatim copy of `Work.BoseB1Cube.pairCountPayment`
(`Submission/Work/BoseB1Cube/cubeFlatArm_holds.lean:87`), whose module cannot sit in a
holder-free import cone. -/
theorem pairCountPaymentLower {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (E3)} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ)
    (hN2 : 0 < ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) :
    (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
    ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  have h := Work.BoseFixB1S.boxFlatSqJensen (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA
    hAc hΦc
  have hIne : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) ≠ 0 := ne_of_gt hN2
  have hdiv : (((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    have h' := div_le_div_of_nonneg_right h hN2.le
    rwa [mul_div_cancel_left₀ _ hIne] at h'
  have hrew : (((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
      = (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
          / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
    rw [sub_div, mul_div_cancel_right₀ _ hIne]
  rwa [hrew] at hdiv

end Work.BoseB1Cube
