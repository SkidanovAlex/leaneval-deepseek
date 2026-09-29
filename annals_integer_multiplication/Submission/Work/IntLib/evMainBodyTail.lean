import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.evChainDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base

namespace Work.IntLib

open HvdH

/-- The head glyph of the encoding of a `cons`-chain `intList l` says whether `l` is empty. -/
theorem evMainBodyTail_headD (l : List ℕ) (rest : List Glyph) :
    (Val.enc (intList l) ++ rest).headD Glyph.eos =
      if l = [] then Glyph.nil else Glyph.cons := by
  cases l with
  | nil => rw [enc_intList_nil]; simp
  | cons h t => rw [enc_intList_cons]; simp

/-- The tail of the body of the main loop of the `evalPoly` word: peek the next glyph of the chain
(giving `cons` exactly when the chain `tl` is nonempty) and set the loop register `rLp` accordingly.
Cost `3`; stack 0 is untouched. -/
theorem evMainBodyTail (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph) (tl : List ℕ) (Z : List HvdH.Glyph)
    (hX : X 0 = HvdH.Val.enc (HvdH.intList tl) ++ Z) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main
        (Work.Layout.seqs [.peek Work.IntLib.aC Work.IntLib.rY,
          .ite Work.IntLib.rY HvdH.Glyph.cons (.set Work.IntLib.rLp Work.IntLib.fGo)
            (.set Work.IntLib.rLp Work.IntLib.fStop)]) ⟨g, X⟩ s' n ∧
      n ≤ 3 ∧ s'.stk = X ∧
      s'.reg Work.IntLib.rLp = (if tl = [] then Work.IntLib.fStop else Work.IntLib.fGo) := by
  have hXaC : X aC = Val.enc (intList tl) ++ Z := hX
  have hflag : (X aC).headD Glyph.eos = if tl = [] then Glyph.nil else Glyph.cons := by
    rw [hXaC]; exact evMainBodyTail_headD tl Z
  have hpeek : Work.Layout.Ev main (.peek aC rY) ⟨g, X⟩
      ⟨Function.update g rY ((X aC).headD Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main aC rY g X
  by_cases hnil : tl = []
  · have hhd : (X aC).headD Glyph.eos = Glyph.nil := by rw [hflag]; simp [hnil]
    rw [hhd] at hpeek
    have hset : Work.Layout.Ev main (.set rLp fStop)
        ⟨Function.update g rY Glyph.nil, X⟩
        ⟨Function.update (Function.update g rY Glyph.nil) rLp fStop, X⟩ 1 :=
      Work.Layout.ev_set' main rLp fStop _ X
    have hite : Work.Layout.Ev main
        (.ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop))
        ⟨Function.update g rY Glyph.nil, X⟩
        ⟨Function.update (Function.update g rY Glyph.nil) rLp fStop, X⟩ 2 :=
      Work.Layout.Ev.iteF (by
        show Function.update g rY Glyph.nil rY ≠ Glyph.cons
        rw [Function.update_self]
        intro h; cases h) hset
    refine ⟨⟨Function.update (Function.update g rY Glyph.nil) rLp fStop, X⟩, 3,
      ?_, le_rfl, rfl, ?_⟩
    · exact Work.Layout.Ev.seqs_cons
        (cs := [.ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop)]) hpeek hite
    · simp [hnil]
  · have hhd : (X aC).headD Glyph.eos = Glyph.cons := by rw [hflag]; simp [hnil]
    rw [hhd] at hpeek
    have hset : Work.Layout.Ev main (.set rLp fGo)
        ⟨Function.update g rY Glyph.cons, X⟩
        ⟨Function.update (Function.update g rY Glyph.cons) rLp fGo, X⟩ 1 :=
      Work.Layout.ev_set' main rLp fGo _ X
    have hite : Work.Layout.Ev main
        (.ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop))
        ⟨Function.update g rY Glyph.cons, X⟩
        ⟨Function.update (Function.update g rY Glyph.cons) rLp fGo, X⟩ 2 :=
      Work.Layout.Ev.iteT (by
        show Function.update g rY Glyph.cons rY = Glyph.cons
        rw [Function.update_self]) hset
    refine ⟨⟨Function.update (Function.update g rY Glyph.cons) rLp fGo, X⟩, 3,
      ?_, le_rfl, rfl, ?_⟩
    · exact Work.Layout.Ev.seqs_cons
        (cs := [.ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop)]) hpeek hite
    · simp [hnil]

end Work.IntLib
