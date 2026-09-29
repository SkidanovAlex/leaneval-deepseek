-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/groupStop_ev.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.chunksProof
namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

/-- When the element stack `sT` already shows the sentinel `gSent` (no elements left to chunk),
`groupBody` takes the stopping branch: in 3 steps it sets `rLoopG := eos` and restores every
stack. -/
theorem groupStop_ev {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {T0 : List HvdH.Glyph}
    (hT : X Work.Resample.PBChunk.sT = Work.Layout.gSent :: T0) :
    ∃ s', Work.Layout.Ev main Work.Resample.PBChunk.groupBody ⟨g, X⟩ s' 3 ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
      (∀ j : HvdH.Stk, s'.stk j = X j) := by
  -- step 1: peek the sentinel into `rE`
  have hpeek : Ev main (.peek sT rE) ⟨g, X⟩ ⟨Function.update g rE gSent, X⟩ 1 := by
    have h := ev_peek' main sT rE g X
    rw [hT] at h
    simpa using h
  -- step 2+3: the test succeeds, so take the `then` branch `set rLoopG eos`
  obtain ⟨s₂, hset, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos)
      (g := Function.update g rE gSent) (X := X)
  have hcond : (Function.update g rE gSent) rE = gSent := Function.update_self rE gSent g
  have hit : Ev main (.ite rE gSent (.set rLoopG Glyph.eos)
      (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
        .set rLoopG gCont])) ⟨Function.update g rE gSent, X⟩ s₂ 2 :=
    Ev.iteT hcond hset
  refine ⟨s₂, ?_, hs₂r, fun j => hs₂f j⟩
  have hbody : Ev main (seqs [.peek sT rE, .ite rE gSent (.set rLoopG Glyph.eos)
      (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
        .set rLoopG gCont])]) ⟨g, X⟩ s₂ 3 :=
    Ev.seq' hpeek hit (by omega)
  simpa [groupBody] using hbody

end Work.Resample.PBChunk