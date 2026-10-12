import ChallengeDeps
import Submission.Work.BoseBogFS.View
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ViewBridge` — from the canonical view to this chapter's

Node `D-FS`'s `Work.BoseBoxFock.RViewFS` and this chapter's `Work.BoseBogFS.RViewFS` are the
same proposition in 22 of their 23 conjuncts.  The one difference is conjunct 12: the
canonical view pins the kinetic symbol to the *concrete* profile,
`E.tau = tauSm …` (`Work.BoseBoxFock.tauProf`), while this chapter's copy carries the
equivalent existential pin `tauSmPin F E : ∃ φ, …` (no `Classical.choose` in the statements).

This module bridges the two: **any consumer holding the canonical view can use the whole of
this chapter's view-level API** (`bogNumeric_of_viewFS`, `abs_W1_le_viewFS`,
`W1_lowband_viewFS`, and all of `View.lean`'s projections).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The canonical pin `E.tau = tauSm …` (with the parameter identifications of the same
conjunction) implies the existential pin `tauSmPin` of this chapter. -/
theorem tauSmPin_of_tauPin {F : FockData Mode} {E : Q3Env Mode} {eTp sp dp ℓp : ℝ}
    (h : E.tau = (fun k => Work.BoseBoxFock.tauSm eTp sp dp ℓp (F.kmom k)))
    (hd : E.d = dp) (hs : E.s = sp) (heT : E.eT = eTp) (hℓ : E.ell = ℓp) :
    tauSmPin F E := by
  refine ⟨Work.BoseBoxFock.tauProf,
    Work.BoseBoxFock.tauProf_spec.1,
    Work.BoseBoxFock.tauProf_spec.2.1,
    Work.BoseBoxFock.tauProf_spec.2.2.1,
    Work.BoseBoxFock.tauProf_spec.2.2.2.1,
    Work.BoseBoxFock.tauProf_spec.2.2.2.2.1, ?_⟩
  funext k
  have hh := congrFun h k
  rw [← hd, ← hs, ← heT, ← hℓ] at hh
  simpa only [Work.BoseBoxFock.tauSm] using hh

/-- **The canonical view implies this chapter's.** -/
theorem RViewFS_of_canonical {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {F : FockData Mode}
    {T : Work.BoseB7A.TildeData F} {E : Q3Env Mode} {gHat0 : ℝ}
    (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) : RViewFS v h μ F T E gHat0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩
  exact tauSmPin_of_tauPin (F := F) (E := E)
    (eTp := (paramsAt μ (a v)).eT) (sp := (paramsAt μ (a v)).s) (dp := (paramsAt μ (a v)).d)
    (ℓp := ell v μ) h12 h7 h8 h9 h4

end Work.BoseBogFS
