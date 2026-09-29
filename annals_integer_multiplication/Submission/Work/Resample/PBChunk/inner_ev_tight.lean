-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/inner_ev_tight.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.chunksProof
set_option linter.unusedSimpArgs false

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

/-!
# A tight cost bound for the element loop of `chunksOf`

`Work.Resample.PBChunk.inner_ev` (in `chunksProof.lean`) bounds the cost of `innerProg` by
`40 * ((ys.map vsz).sum + ys.length + 1)`, which is enough for the *asymptotic* statement but not
for the additive-shape estimate the caller needs.  Here we redo the same induction with the
*exact* costs:

* `elemBody_move` costs `16 * (vsz y + 1) + 8` for the element `y`;
* the loop test costs one step per iteration;
* the terminating test costs 3 steps (its own) + 1 step (the loop test).

Summing over `ys` and adding the initial `set rH gCont` gives exactly
`16 * (ys.map vsz).sum + 25 * ys.length + 6`.
-/

/-- `elemLoop` with the exact cost. -/
theorem elemLoop_tight {main : Cmd} :
    ∀ (ys : List Val) (g : Reg → Glyph) (X : Stk → List Glyph) (A0 T0 W0 : List Glyph),
      g rH = gCont → X sW = List.replicate ys.length gPend ++ gSent :: W0 →
      X sT = (ys.map Val.enc).flatten ++ T0 → X 0 = A0 →
      ∃ s', loopRuns main rH gCont elemBody (ys.length + 1) ⟨g, X⟩ s'
          (16 * (ys.map vsz).sum + 25 * ys.length + 4) ∧
        s'.stk 0 = twist ys ++ A0 ∧ s'.stk sT = T0 ∧ s'.stk sW = gSent :: W0 ∧
        s'.reg rH = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  intro ys
  induction ys with
  | nil =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hW' : X sW = gSent :: W0 := by simpa using hW
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
        elemBody_stop (main := main) (g := g) (X := X) (W0 := W0) hW'
      refine ⟨s₁, ?_, ?_, ?_, ?_, hreg₁, ?_⟩
      · have h := loopRuns.one (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁
        simpa using h
      · simp only [hs₁0, h0, twist, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁T, hT, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁W, hW']
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₁ j]
  | cons y ys' ih =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hT' : X sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0) := by
        rw [hT, List.map_cons, List.flatten_cons, List.append_assoc]
      have hW' : X sW = gPend :: (List.replicate ys'.length gPend ++ gSent :: W0) := by
        have hlen : (y :: ys').length = ys'.length + 1 := rfl
        rw [hW, hlen, List.replicate_succ, List.cons_append]
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
        elemBody_move (main := main) (g := g) (X := X) (y := y) (ys' := ys')
          (k' := ys'.length) hW' hT' h0
      obtain ⟨s₂, hrun₂, hs₂0, hs₂T, hs₂W, hreg₂, hfr₂⟩ :=
        ih s₁.reg s₁.stk (Glyph.cons :: y.enc ++ A0) T0 W0 hreg₁ hs₁W hs₁T hs₁0
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁ hrun₂ ?_,
        ?_, ?_, ?_, hreg₂, ?_⟩
      · simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
      · rw [hs₂0, twist_cons, List.append_assoc]
      · exact hs₂T
      · exact hs₂W
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₂ j hj1 hj2 hj3 hj4 hj5, hfr₁ j hj1 hj2 hj3 hj4 hj5]

theorem inner_ev_tight {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ys : List HvdH.Val} {A0 T0 W0 : List HvdH.Glyph}
    (hW : X Work.Resample.PBChunk.sW = List.replicate ys.length Work.Layout.gPend ++ Work.Layout.gSent :: W0)
    (hT : X Work.Resample.PBChunk.sT = (ys.map HvdH.Val.enc).flatten ++ T0) (h0 : X 0 = A0) :
    ∃ s' n, Work.Layout.Ev main Work.Resample.PBChunk.innerProg ⟨g, X⟩ s' n ∧
      n ≤ 16 * (ys.map HvdH.vsz).sum + 25 * ys.length + 6 ∧
      s'.stk 0 = Work.Resample.PBChunk.twist ys ++ A0 ∧
      s'.stk Work.Resample.PBChunk.sT = T0 ∧
      s'.stk Work.Resample.PBChunk.sW = Work.Layout.gSent :: W0 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Resample.PBChunk.sT → j ≠ Work.Resample.PBChunk.sW →
        j ≠ Work.Resample.PBChunk.sB → j ≠ Work.Resample.PBChunk.sC → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hr₀, -, hf₀⟩ :=
    step_set (main := main) (r := rH) (c := gCont) (g := g) (X := X)
  have hW' : s₀.stk sW = List.replicate ys.length gPend ++ gSent :: W0 := by rw [hf₀ sW, hW]
  have hT' : s₀.stk sT = (ys.map Val.enc).flatten ++ T0 := by rw [hf₀ sT, hT]
  have h0' : s₀.stk 0 = A0 := by rw [hf₀ 0, h0]
  obtain ⟨s₁, hrun₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
    elemLoop_tight (main := main) ys s₀.reg s₀.stk A0 T0 W0 (by rw [hr₀]) hW' hT' h0'
  have hmain : Ev main innerProg ⟨g, X⟩ s₁ (16 * (ys.map vsz).sum + 25 * ys.length + 6) := by
    unfold innerProg
    refine Ev.seq' hev₀ (loopRuns.eval hrun₁ (by rw [hreg₁]; decide)) ?_
    omega
  exact ⟨s₁, _, hmain, le_rfl, hs₁0, hs₁T, hs₁W, fun j hj1 hj2 hj3 hj4 hj5 => by
    rw [hfr₁ j hj1 hj2 hj3 hj4 hj5, hf₀ j]⟩

end Work.Resample.PBChunk