import ChallengeDeps
import Submission.Work.BoseFixR.All.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/HonestEnvParity.lean`

The environment parity of the honest family `Work.BoseBoxFock.HonestBoxFam`:
the kinetic symbol `E.tau` and the potential kernel `E.W1` are **even** on the
mode lattice `Lab N` of the box.

## Where the parity comes from

`HonestBoxFam v h fc fu HM μ` is the *concrete* family of
`Submission/Work/BoseBoxFock/Defs.lean`, and its environment is
`KzEnvHon v h μ F fc fu N`, whose `tau`/`W1` fields are *definitionally*

* `E.tau k = tauSm P.eT P.s P.d ℓ (F.kmom k)`, and
* `E.W1 k = uvCut fu (uvRad ℓ N) (F.kmom k) * chat (W1fun v h ℓ) (F.kmom k)`.

Both factors are even in the momentum argument, for three reasons:

1. the momentum label is odd under negation on the *odd* modulus `2N+1`
   (`Work.BoseBoxFock.kmomLab_neg`: `valMinAbs (-x) = -valMinAbs x`), so
   `F.kmom (-k) = -(F.kmom k)`;
2. `tauSm` and `uvCut` are functions of `‖·‖` alone, so `norm_neg` finishes them;
3. `chat W = Re Ŵ(·)` is even for every *real* `W` (`Work.BoseB7AK.W1rows.chat_neg`,
   from `kinFT u (-p) = conj (kinFT u p)`).

So the parity is a fact about the honest model itself; the view hypothesis
`hview : (HonestBoxFam … μ).viewFSAll v h μ` is *not* needed for it (the view's
kernel pins are satisfied *definitionally* by `KzEnvHon`).  We keep the
hypothesis in the statement — it costs nothing and it is the form the consumer
has in hand — and it is used below only through the trivial remark that it
holds at `μ`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- **The kinetic symbol of the honest family is even.**  At
`(HonestBoxFam v h fc fu HM μ).E.tau` the value is
`tauSm … (F.kmom k)` with `F.kmom = kmomLab ℓ N`, and `kmomLab` is odd while
`tauSm` depends on `‖·‖` only. -/
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
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ) :
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

end Work.BoseFixR.All
