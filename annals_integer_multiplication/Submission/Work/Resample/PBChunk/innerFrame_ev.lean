-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/innerFrame_ev.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.chunksProof
set_option autoImplicit false

/-!
# `innerFrame_ev`: the element loop of `chunksOf` restores ALL its scratch stacks

`Work.Resample.PBChunk.inner_ev` (`chunksProof.lean`) proves a frame condition for `innerProg` which
excludes the `mvVal` buffer `sB` and counter `sC` from the restored stacks.  Because `mvVal`
restores its two scratch stacks exactly (`Work.Layout.mvVal_ev_full`), these two stacks are in
fact restored as well.  This file redoes the induction of `elemBody_move` / `elemLoop` carrying
`sB` and `sC` through, and concludes the strengthened frame.
-/

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

theorem elemBody_move_full {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {y : Val}
    {ys' : List Val} {k' : ℕ} {A0 T0 W0 : List Glyph}
    (hW : X sW = gPend :: (List.replicate k' gPend ++ gSent :: W0))
    (hT : X sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0)) (h0 : X 0 = A0) :
    ∃ s', Ev main elemBody ⟨g, X⟩ s' (16 * (vsz y + 1) + 8) ∧
      s'.stk 0 = Glyph.cons :: y.enc ++ A0 ∧
      s'.stk sT = (ys'.map Val.enc).flatten ++ T0 ∧
      s'.stk sW = List.replicate k' gPend ++ gSent :: W0 ∧
      s'.stk sB = X sB ∧ s'.stk sC = X sC ∧
      s'.reg rH = gCont ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁W, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sW) (r := rE) hW
  obtain ⟨s₂, hev₂, hs₂W, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sW) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁W
  have hT₂ : s₂.stk sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0) := by
    rw [hs₂f sT (by decide : sT ≠ sW), hs₁f sT (by decide : sT ≠ sW), hT]
  have h0₂ : s₂.stk 0 = A0 := by
    rw [hs₂f 0 (by decide : 0 ≠ sW), hs₁f 0 (by decide : 0 ≠ sW), h0]
  obtain ⟨s₃, hn₃, hev₃, hb₃, hs₃T, hs₃0, hs₃B, hs₃C, hs₃f⟩ :=
    mvVal_ev_full (main := main) (a := sT) (b := 0) (c := sB) (d := sC)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₂.reg) (X := s₂.stk) (v := y) (A := (ys'.map Val.enc).flatten ++ T0) (B := A0)
      hT₂ h0₂
  have h3 : Ev main (mvVal sT 0 sB sC) s₂ s₃ (16 * (vsz y + 1)) := hev₃.mono hb₃
  obtain ⟨s₄, hev₄, hs₄0, hs₄f, hs₄r, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.cons) (g := s₃.reg) (X := s₃.stk)
  obtain ⟨s₅, hev₅, hs₅r, -, hs₅f⟩ :=
    step_set (main := main) (r := rH) (c := gCont) (g := s₄.reg) (X := s₄.stk)
  have hcond : ¬ (s₁.reg rE = gSent) := by rw [hs₁r]; exact gPend_ne_gSent
  have h34 : Ev main (seqs [pushK 0 Glyph.cons, .set rH gCont]) s₃ s₅ 3 :=
    Ev.seq' hev₄ hev₅ (by omega)
  have h234 : Ev main (seqs [mvVal sT 0 sB sC, pushK 0 Glyph.cons, .set rH gCont]) s₂ s₅
      (16 * (vsz y + 1) + 3) := Ev.seq' h3 h34 (by omega)
  have h1234 : Ev main (seqs [.pop sW rE, mvVal sT 0 sB sC, pushK 0 Glyph.cons,
      .set rH gCont]) s₁ s₅ (1 + (16 * (vsz y + 1) + 3)) := Ev.seq' hev₂ h234 (by omega)
  have hbody : Ev main elemBody ⟨g, X⟩ s₅ (16 * (vsz y + 1) + 8) :=
    Ev.seq' hev₁ (Ev.iteF hcond h1234) (by omega)
  refine ⟨s₅, hbody, ?_, ?_, ?_, ?_, ?_, hs₅r, ?_⟩
  · simp only [hs₅f 0, hs₄0, hs₃0, List.cons_append]
  · rw [hs₅f sT, hs₄f sT (by decide : sT ≠ 0), hs₃T]
  · rw [hs₅f sW, hs₄f sW (by decide : sW ≠ 0),
      hs₃f sW (by decide : sW ≠ sT) (by decide : sW ≠ 0) (by decide : sW ≠ sB)
        (by decide : sW ≠ sC), hs₂W]
  · rw [hs₅f sB, hs₄f sB (by decide : sB ≠ 0), hs₃B, hs₂f sB (by decide : sB ≠ sW),
      hs₁f sB (by decide : sB ≠ sW)]
  · rw [hs₅f sC, hs₄f sC (by decide : sC ≠ 0), hs₃C, hs₂f sC (by decide : sC ≠ sW),
      hs₁f sC (by decide : sC ≠ sW)]
  · intro j hj1 hj2 hj3 hj4 hj5
    rw [hs₅f j, hs₄f j hj1,
      hs₃f j hj2 hj1 hj4 hj5, hs₂f j hj3, hs₁f j hj3]

theorem elemLoop_full {main : Cmd} :
    ∀ (ys : List Val) (g : Reg → Glyph) (X : Stk → List Glyph) (A0 T0 W0 : List Glyph),
      g rH = gCont → X sW = List.replicate ys.length gPend ++ gSent :: W0 →
      X sT = (ys.map Val.enc).flatten ++ T0 → X 0 = A0 →
      ∃ s', loopRuns main rH gCont elemBody (ys.length + 1) ⟨g, X⟩ s'
          (30 * ((ys.map vsz).sum + ys.length + 1)) ∧
        s'.stk 0 = twist ys ++ A0 ∧ s'.stk sT = T0 ∧ s'.stk sW = gSent :: W0 ∧
        s'.stk sB = X sB ∧ s'.stk sC = X sC ∧
        s'.reg rH = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  intro ys
  induction ys with
  | nil =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hW' : X sW = gSent :: W0 := by simpa using hW
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
        elemBody_stop (main := main) (g := g) (X := X) (W0 := W0) hW'
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁) (by omega),
        ?_, ?_, ?_, ?_, ?_, hreg₁, ?_⟩
      · simp only [hs₁0, h0, twist, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁T, hT, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁W, hW']
      · rw [hfr₁ sB]
      · rw [hfr₁ sC]
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₁ j]
  | cons y ys' ih =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hT' : X sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0) := by
        rw [hT, List.map_cons, List.flatten_cons, List.append_assoc]
      have hW' : X sW = gPend :: (List.replicate ys'.length gPend ++ gSent :: W0) := by
        have hlen : (y :: ys').length = ys'.length + 1 := rfl
        rw [hW, hlen, List.replicate_succ, List.cons_append]
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hs₁B, hs₁C, hreg₁, hfr₁⟩ :=
        elemBody_move_full (main := main) (g := g) (X := X) (y := y) (ys' := ys')
          (k' := ys'.length) hW' hT' h0
      obtain ⟨s₂, hrun₂, hs₂0, hs₂T, hs₂W, hs₂B, hs₂C, hreg₂, hfr₂⟩ :=
        ih s₁.reg s₁.stk (Glyph.cons :: y.enc ++ A0) T0 W0 hreg₁ hs₁W hs₁T hs₁0
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁ hrun₂
        (by simp only [List.length_cons, List.map_cons, List.sum_cons]; omega),
        ?_, ?_, ?_, ?_, ?_, hreg₂, ?_⟩
      · rw [hs₂0, twist_cons, List.append_assoc]
      · exact hs₂T
      · exact hs₂W
      · rw [hs₂B, hs₁B]
      · rw [hs₂C, hs₁C]
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₂ j hj1 hj2 hj3 hj4 hj5, hfr₁ j hj1 hj2 hj3 hj4 hj5]

theorem innerFrame_ev {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ys : List HvdH.Val} {k : ℕ}
    {A0 T0 W0 : List HvdH.Glyph} (hk : ys.length = k)
    (hW : X Work.Resample.PBChunk.sW = List.replicate k Work.Layout.gPend ++ Work.Layout.gSent :: W0)
    (hT : X Work.Resample.PBChunk.sT = (ys.map HvdH.Val.enc).flatten ++ T0) (h0 : X 0 = A0) :
    ∃ s' n, Work.Layout.Ev main Work.Resample.PBChunk.innerProg ⟨g, X⟩ s' n ∧
      n ≤ 40 * ((ys.map HvdH.vsz).sum + k + 1) ∧
      s'.stk 0 = Work.Resample.PBChunk.twist ys ++ A0 ∧ s'.stk Work.Resample.PBChunk.sT = T0 ∧
      s'.stk Work.Resample.PBChunk.sW = Work.Layout.gSent :: W0 ∧
      s'.stk Work.Resample.PBChunk.sB = X Work.Resample.PBChunk.sB ∧
      s'.stk Work.Resample.PBChunk.sC = X Work.Resample.PBChunk.sC ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Resample.PBChunk.sT → j ≠ Work.Resample.PBChunk.sW →
        j ≠ Work.Resample.PBChunk.sB → j ≠ Work.Resample.PBChunk.sC → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hr₀, -, hf₀⟩ :=
    step_set (main := main) (r := rH) (c := gCont) (g := g) (X := X)
  have hW' : s₀.stk sW = List.replicate ys.length gPend ++ gSent :: W0 := by
    rw [hf₀ sW, hW, hk]
  have hT' : s₀.stk sT = (ys.map Val.enc).flatten ++ T0 := by rw [hf₀ sT, hT]
  have h0' : s₀.stk 0 = A0 := by rw [hf₀ 0, h0]
  obtain ⟨s₁, hrun₁, hs₁0, hs₁T, hs₁W, hs₁B, hs₁C, hreg₁, hfr₁⟩ :=
    elemLoop_full (main := main) ys s₀.reg s₀.stk A0 T0 W0 (by rw [hr₀]) hW' hT' h0'
  have hmain : Ev main innerProg ⟨g, X⟩ s₁ (40 * ((ys.map vsz).sum + k + 1)) := by
    unfold innerProg
    refine Ev.seq' hev₀ (loopRuns.eval hrun₁ (by rw [hreg₁]; decide)) (by rw [hk]; omega)
  refine ⟨s₁, _, hmain, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₁0]
  · rw [hs₁T]
  · rw [hs₁W]
  · rw [hs₁B, hf₀ sB]
  · rw [hs₁C, hf₀ sC]
  · intro j hj1 hj2 hj3 hj4 hj5
    rw [hfr₁ j hj1 hj2 hj3 hj4 hj5, hf₀ j]

end Work.Resample.PBChunk