import Mathlib
import Submission.Work.Layout.Take.Basic

namespace Work.Layout.Take

open HvdH

/-- The *stopping* iteration of the comparison loop body `cmpBody` of
`Submission/Work/Layout/Take/Defs.lean` (namespace `Work.Layout`).  `cmpBody` is
`peek sD rE_x ;; ite rE_x gU (peek sBit rE_x ;; ite rE_x gMark (set rG eos) (pop sD rE_x ;; decProg ;;
set rE_x gU ;; push sDp rE_x ;; set rG gCont_x)) (set rG eos)`, and it stops — setting `rG := eos` so
that the enclosing `loop rG gCont_x cmpBody` exits — exactly when the top of `sD` is the frame
`gMark` (`len = 0`, i.e. the unary counter is exhausted, so the outer `ite` takes its else branch)
or, when `len > 0`, when the top of `sBit` is `gMark` (`K = 0`, i.e. the binary counter has
decremented to `0`, since `bitsG_x 0.bits = []`, so the inner `ite` takes its then branch).  Hence
the hypothesis `hstop : K = 0 ∨ len = 0`.

In both cases nothing but the register `rG` changes: every stack of the resulting state equals the
corresponding stack of the initial state, and the cost is at most `5` (1 `peek` + 1 test + 1 `set`
in the `len = 0` case, 1+1+1+1+1 in the `K = 0` case).  Useful: the `Ev` primitives of
`Submission/Work/Layout/Base.lean` (`ev_peek'`, `ev_set'`, `Ev.seq'`, `Ev.seqs_cons`, `Ev.iteT`,
`Ev.iteF`) and `Work.Layout.gMark_ne_gU`. -/
theorem cmpBody_stop (main : HvdH.Cmd) (K len : ℕ) (hstop : K = 0 ∨ len = 0)
    (R Drest : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (hbit : X Work.Layout.sBit = Work.Layout.bitsG_x K.bits ++ Work.Layout.gMark :: R)
    (hD : X Work.Layout.sD = List.replicate len Work.Layout.gU ++ Work.Layout.gMark :: Drest) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.cmpBody ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.reg Work.Layout.rG = HvdH.Glyph.eos ∧ (∀ j, s'.stk j = X j) := by
  -- the two possible stopping configurations; the inner `ite` counts one test more than
  -- the outer one, so the `len = 0` case costs `3` and the `K = 0`, `len > 0` case costs `5`.
  by_cases hlen : len = 0
  · -- `len = 0`: the top of `sD` is the frame marker, so the outer `ite` takes its else branch
    subst hlen
    have hheadD : (X Work.Layout.sD).headD Glyph.eos = Work.Layout.gMark := by
      rw [hD]; rfl
    have h1 : Ev main (.peek Work.Layout.sD Work.Layout.rE_x) ⟨g, X⟩
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩ 1 := by
      have h := ev_peek' main Work.Layout.sD Work.Layout.rE_x g X
      rw [hheadD] at h
      exact h
    have h2 : Ev main (.set Work.Layout.rG Glyph.eos)
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩
        ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
          Work.Layout.rG Glyph.eos, X⟩ 1 :=
      ev_set' main Work.Layout.rG Glyph.eos _ _
    have h3 : Ev main (.ite Work.Layout.rE_x Work.Layout.gU
          (seqs [.peek Work.Layout.sBit Work.Layout.rE_x,
            .ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG Glyph.eos)
              (seqs [.pop Work.Layout.sD Work.Layout.rE_x, decProg,
                .set Work.Layout.rE_x Work.Layout.gU, .push Work.Layout.sDp Work.Layout.rE_x,
                .set Work.Layout.rG Work.Layout.gCont_x])])
          (.set Work.Layout.rG Glyph.eos))
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩
        ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
          Work.Layout.rG Glyph.eos, X⟩ 2 := by
      refine Ev.iteF ?_ h2
      show Function.update g Work.Layout.rE_x Work.Layout.gMark Work.Layout.rE_x ≠ Work.Layout.gU
      rw [Function.update_self]
      exact gMark_ne_gU
    refine ⟨⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
        Work.Layout.rG Glyph.eos, X⟩, 3, ?_, by norm_num, ?_, ?_⟩
    · unfold cmpBody
      exact Ev.seq' h1 h3 (by omega)
    · show Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
        Work.Layout.rG Glyph.eos Work.Layout.rG = Glyph.eos
      rw [Function.update_self]
    · intro j; rfl
  · -- `len ≠ 0` and `K = 0`: the top of `sD` is a unit and the top of `sBit` is the frame marker,
    -- so the outer `ite` takes its then branch and the inner one its then branch as well
    have hK : K = 0 := by rcases hstop with h | h; exact h; exact absurd h hlen
    have hheadD : (X Work.Layout.sD).headD Glyph.eos = Work.Layout.gU := by
      rw [hD]
      cases len with
      | zero => exact absurd rfl hlen
      | succ k => rfl
    have hheadB : (X Work.Layout.sBit).headD Glyph.eos = Work.Layout.gMark := by
      rw [hbit, hK, Nat.zero_bits, bitsG_nil]
      rfl
    have h1 : Ev main (.peek Work.Layout.sD Work.Layout.rE_x) ⟨g, X⟩
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gU, X⟩ 1 := by
      have h := ev_peek' main Work.Layout.sD Work.Layout.rE_x g X
      rw [hheadD] at h
      exact h
    have h2 : Ev main (.peek Work.Layout.sBit Work.Layout.rE_x)
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gU, X⟩
        ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark, X⟩ 1 := by
      have h := ev_peek' main Work.Layout.sBit Work.Layout.rE_x
        (Function.update g Work.Layout.rE_x Work.Layout.gU) X
      rw [hheadB] at h
      exact h
    have h3 : Ev main (.set Work.Layout.rG Glyph.eos)
        ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark, X⟩
        ⟨Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos, X⟩ 1 :=
      ev_set' main Work.Layout.rG Glyph.eos _ _
    have h4 : Ev main (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG Glyph.eos)
          (seqs [.pop Work.Layout.sD Work.Layout.rE_x, decProg,
            .set Work.Layout.rE_x Work.Layout.gU, .push Work.Layout.sDp Work.Layout.rE_x,
            .set Work.Layout.rG Work.Layout.gCont_x]))
        ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark, X⟩
        ⟨Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos, X⟩ 2 := by
      refine Ev.iteT ?_ h3
      show Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
        Work.Layout.rE_x Work.Layout.gMark Work.Layout.rE_x = Work.Layout.gMark
      rw [Function.update_self]
    have h5 : Ev main (.seq (.peek Work.Layout.sBit Work.Layout.rE_x)
          (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG Glyph.eos)
            (seqs [.pop Work.Layout.sD Work.Layout.rE_x, decProg,
              .set Work.Layout.rE_x Work.Layout.gU, .push Work.Layout.sDp Work.Layout.rE_x,
              .set Work.Layout.rG Work.Layout.gCont_x])))
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gU, X⟩
        ⟨Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos, X⟩ 3 :=
      Ev.seq' h2 h4 (by omega)
    have h6 : Ev main (.ite Work.Layout.rE_x Work.Layout.gU
          (seqs [.peek Work.Layout.sBit Work.Layout.rE_x,
            .ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG Glyph.eos)
              (seqs [.pop Work.Layout.sD Work.Layout.rE_x, decProg,
                .set Work.Layout.rE_x Work.Layout.gU, .push Work.Layout.sDp Work.Layout.rE_x,
                .set Work.Layout.rG Work.Layout.gCont_x])])
          (.set Work.Layout.rG Glyph.eos))
        ⟨Function.update g Work.Layout.rE_x Work.Layout.gU, X⟩
        ⟨Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
          Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos, X⟩ 4 := by
      refine Ev.iteT ?_ h5
      show Function.update g Work.Layout.rE_x Work.Layout.gU Work.Layout.rE_x = Work.Layout.gU
      rw [Function.update_self]
    refine ⟨⟨Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
        Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos, X⟩, 5, ?_,
      by norm_num, ?_, ?_⟩
    · unfold cmpBody
      exact Ev.seq' h1 h6 (by omega)
    · show Function.update (Function.update (Function.update g Work.Layout.rE_x Work.Layout.gU)
        Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rG Glyph.eos Work.Layout.rG = Glyph.eos
      rw [Function.update_self]
    · intro j; rfl

end Work.Layout.Take
