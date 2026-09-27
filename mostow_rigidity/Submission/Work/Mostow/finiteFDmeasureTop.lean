import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.volH1_univ_eq_top

/-!
# `Work.Mostow.finiteFDmeasureTop`

The hyperbolic line `ℍ¹ = E 1` has infinite total hyperbolic volume
(`Work.Mostow.volH1_univ_eq_top`).  Hence a *fundamental domain* `DY` of the action of a **finite**
subgroup `D ≤ PO(1,1)` on `ℍ¹` has infinite volume as well: the `|D|` translates of `DY` cover
`ℍ¹` up to a null set and are pairwise a.e. disjoint, so
`volH 1 univ = |D| • volH 1 DY` (`IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self`),
and a nonzero `ℕ`-multiple of an element of `ℝ≥0∞` is `⊤` only if that element is `⊤`.

The `PO 1 1`-action on `ℍ¹` is only an `SMul` (the action laws are the hypothesis `POActionProp`),
so the required `MulAction` instances and the measure-preservation of the action are installed
from the area hypotheses `POActionProp 1` and `HypIsometryProp 1` before applying Mathlib's
fundamental domain lemma.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- In `ℝ≥0∞`, a nonzero natural multiple `k • x = ⊤` forces `x = ⊤`. -/
lemma eq_top_of_nsmul_eq_top {k : ℕ} (hk : k ≠ 0) {x : ℝ≥0∞} (h : k • x = ⊤) : x = ⊤ := by
  rw [nsmul_eq_mul] at h
  rcases ENNReal.mul_eq_top.mp h with ⟨-, hx⟩ | ⟨hk', -⟩
  · exact hx
  · exact absurd hk' (ENNReal.natCast_ne_top k)

theorem finiteFDmeasureTop (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (D : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1)) [Finite D]
    (DY : Set (Submission.Mostow.E 1))
    (hFD : MeasureTheory.IsFundamentalDomain D DY (Submission.Mostow.volH 1)) :
    Submission.Mostow.volH 1 DY = ⊤ := by
  have hB : POBasic 1 := POBasic.ofProp hA
  have hId : HypIsoData 1 := HypIsoData.ofProp hI
  -- the `PO 1 1`-action on `ℍ¹` is a `MulAction`, and so is its restriction to `D`
  letI : MulAction (PO 1 1) (E 1) :=
    { one_smul := hB.one_smul
      mul_smul := hB.mul_smul }
  letI : MulAction D (E 1) := inferInstance
  -- the action is measurable and preserves the hyperbolic volume
  haveI : MeasurableConstSMul D (E 1) :=
    ⟨fun c => (hId.contDiff_smul (c : PO 1 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure D (E 1) (volH 1) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO 1 1)).measure_preimage hs.nullMeasurableSet⟩
  -- the translates of a fundamental domain of the finite group `D` tile `ℍ¹`
  have hcard := hFD.measure_eq_card_smul_of_smul_ae_eq_self (t := (Set.univ : Set (E 1)))
    (fun g => by rw [Set.smul_set_univ])
  rw [Set.univ_inter, volH1_univ_eq_top] at hcard
  exact eq_top_of_nsmul_eq_top (Nat.card_pos (α := D)).ne' hcard.symm

end

end Work.Mostow
