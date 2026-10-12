import ChallengeDeps
import Submission.Work.BoseFixKin.Wiring
import Submission.Work.BoseTop.PerN.HBoxGp_of_scaledState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Handoff` — the `hb`-free interface test at the handoff

The `hb`-free counterpart of `Work.BoseFixGlue.Tests.Handoff.HBoxGp_of_LHYBoxB`: from FS's box
theorem `LHYBoxB`, the bosonic reduction `symBoxReduction v` (node S) and `0 ≤ v`, the
pressure-level two-term target `Work.BoseTop.HBoxGp v η₀ C` follows — now with **no** kinetic
localisation hypothesis.  Composing with the proved
`Work.BoseTop.hpres_of_HBoxGp` gives the corpus hypothesis `hpres` of `theorem_1_2`, so this
module is the consumer-facing entry point of the subproject.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixKin

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix Work.BoseFixGlue

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The handoff, `hb`-free.**  From `LHYBoxB` and the bosonic reduction `symBoxReduction v`
together with `0 ≤ v`, the pressure-level two-term target `HBoxGp v η₀ C` follows. -/
theorem HBoxGp_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hred : Work.BoseTop.symBoxReduction v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGp v η₀ C :=
  Work.BoseTop.PerN.HBoxGp_of_scaledState hv hv1 hred hav.le
    (HBoxGSymStateScaled_of_LHYBoxB hη₀ hη₀' hC hv1 hR hv_supp hav hL)

end Work.BoseFixKin
