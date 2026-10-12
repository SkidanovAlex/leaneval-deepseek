import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/Clean/Parity.lean`

**Why this module exists.**  The honest environment parity
(`Work.BoseFixR.HonestEnvParity` in `Submission/Work/BoseFixR/HonestEnvParity.lean`)
is needed by the environment bundle `EnvFactsAt`, but its module imports
`Submission.Work.BoseFixR.RB5FSFixAux`, which (after the interface change `F9`,
`CloseCond` → `CloseCondFS`) no longer compiles; the missing `.olean` therefore makes
every module of that cone unloadable, including the honest `model_kafz` floor.

This file is a **verbatim copy** of the three theorems of that module with the
gratuitous `RB5FSFixAux` import dropped (`RB5FSFixAux` is not used by their proofs),
re-scoped to the namespace `Work.BoseBoxFock.Clean` so that it can coexist with the
original.  Nothing new is proved here.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBoxFock.Clean

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedSectionVars false

theorem honestBoxFam_tau_even {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (k : Work.BoseBoxFock.Lab (HM μ).N) :
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau (-k)
      = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
  simp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseBoxFock.ellH, Work.BoseBoxFock.tauSm, Work.BoseB4.boxFockData,
    Work.BoseB4.b7FockDataBox, Work.BoseBoxFock.kmomLab_neg, norm_neg]

/-- **The potential kernel of the honest family is even.**  At
`(HonestBoxFam v h fc fu HM μ).E.W1` the value is
`uvCut fu (uvRad ℓ N) (F.kmom k) * chat (W1fun v h ℓ) (F.kmom k)`: the cut-off
depends on `‖·‖` only, and `chat` of a real-valued function is even
(`Work.BoseB7AK.W1rows.chat_neg`). -/
theorem honestBoxFam_W1_even {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (k : Work.BoseBoxFock.Lab (HM μ).N) :
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 (-k)
      = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k := by
  simp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseBoxFock.ellH, Work.BoseB4.boxFockData, Work.BoseB4.b7FockDataBox,
    Work.BoseBoxFock.uvCut, Work.BoseBoxFock.uvRad, Work.BoseBoxFock.kmomLab_neg,
    norm_neg, Work.BoseB7AK.W1rows.chat_neg]

theorem HonestEnvParity {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ) :
    (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau (-k)
          = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k)
      ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 (-k)
          = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) := by
  -- the view is available (its kernel pins hold definitionally at `KzEnvHon`);
  -- the parity itself is a fact about the honest model, proved above.
  have _hview := hview
  exact ⟨honestBoxFam_tau_even, honestBoxFam_W1_even⟩

end Work.BoseBoxFock.Clean
