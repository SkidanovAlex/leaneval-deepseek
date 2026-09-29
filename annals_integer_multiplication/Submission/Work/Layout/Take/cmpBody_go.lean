import Mathlib
import Submission.Work.Layout.Take.Basic

namespace Work.Layout.Take

open HvdH

/-! ## Small list helpers used by `cmpBody_go` -/

/-- a canonical bit string of a positive number is non-empty -/
theorem bits_ne_nil_of_pos {k : ℕ} (hk : 0 < k) : k.bits ≠ [] := by
  intro h
  have h2 : k.bits.length = 0 := by simp [h]
  rw [Nat.size_eq_bits_len] at h2
  have h3 := Nat.size_pos (n := k)
  omega

/-- the head of `replicate n gU ++ rest`, for `0 < n` -/
theorem headD_replicate_gU_append {len : ℕ} (h : 0 < len) (rest : List HvdH.Glyph) :
    (List.replicate len Work.Layout.gU ++ rest).headD HvdH.Glyph.eos = Work.Layout.gU := by
  obtain ⟨m, rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
  simp [List.replicate_succ]

/-- the tail of `replicate n gU ++ rest`, for `0 < n` -/
theorem tail_replicate_gU_append {len : ℕ} (h : 0 < len) (rest : List HvdH.Glyph) :
    (List.replicate len Work.Layout.gU ++ rest).tail
      = List.replicate (len - 1) Work.Layout.gU ++ rest := by
  obtain ⟨m, rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
  simp [List.replicate_succ]

/-- One *working* iteration of the comparison loop body `cmpBody` of
`Submission/Work/Layout/Take/Defs.lean` (namespace `Work.Layout`), the body of
`cmpProg = seqs [.set rG gCont_x, .loop rG gCont_x cmpBody]`.  The body is
`peek sD rE_x ;; ite rE_x gU (peek sBit rE_x ;; ite rE_x gMark (set rG eos) (pop sD rE_x ;; decProg ;;
set rE_x gU ;; push sDp rE_x ;; set rG gCont_x)) (set rG eos)`.  When `sD` still has a unit
(`0 < len`, `X sD = replicate len gU ++ gMark :: Drest`) and the binary counter on `sBit` is
non-zero (`0 < k`, `X sBit = bitsG_x k.bits ++ gMark :: R`), the two `peek`s see `gU` and a `bit`
glyph respectively — so the outer `ite` takes the `gU` branch and the inner one the *else* branch,
after which `decProg` is called on the state with `sD` popped.  `hdec : Work.Layout.DecStep main`
is the specification of `decProg` (it decrements the counter, cost `20 * (tzB k.bits + 2)`,
restoring `sTmp` and every stack other than `sBit`), so the iteration

* consumes one unit of `sD`: `s'.stk sD = replicate (len-1) gU ++ gMark :: Drest`,
* decrements the counter: `s'.stk sBit = bitsG_x (k-1).bits ++ gMark :: R`,
* records the consumed unit on `sDp`: `s'.stk sDp = gU :: X sDp`,
* sets `rG := gCont_x` (the loop continues),
* leaves `sTmp` and every stack outside `{sBit, sD, sDp, sTmp}` untouched,

at cost at most `20 * (tzB k.bits + 2) + 10`.  (Cost count: 1 `peek` + 1 test + 1 `peek` + 1 test +
1 `pop` + `decProg` + 1 `set` + 1 `push` + 1 `set` = `decProg + 8`.)  Useful: the `Ev` primitives
of `Submission/Work/Layout/Base.lean` (`ev_peek'`, `ev_pop'`, `ev_push'`, `ev_set'`, `Ev.seq'`,
`Ev.seqs_cons`, `Ev.iteT`, `Ev.iteF`) and `Work.Layout.gMark_ne_gU`, `gMark_notMem_bitsG_x`. -/
theorem cmpBody_go (main : HvdH.Cmd) (hdec : Work.Layout.DecStep main) (k len : ℕ)
    (hk : 0 < k) (hlen : 0 < len) (R Drest : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph)
    (hbit : X Work.Layout.sBit = Work.Layout.bitsG_x k.bits ++ Work.Layout.gMark :: R)
    (hD : X Work.Layout.sD = List.replicate len Work.Layout.gU ++ Work.Layout.gMark :: Drest) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.cmpBody ⟨g, X⟩ s' n ∧
      n ≤ 20 * (Work.Layout.tzB k.bits + 2) + 10 ∧
      s'.stk Work.Layout.sBit = Work.Layout.bitsG_x (k - 1).bits ++ Work.Layout.gMark :: R ∧
      s'.stk Work.Layout.sD = List.replicate (len - 1) Work.Layout.gU ++ Work.Layout.gMark :: Drest ∧
      s'.stk Work.Layout.sDp = Work.Layout.gU :: X Work.Layout.sDp ∧
      s'.reg Work.Layout.rG = Work.Layout.gCont_x ∧
      s'.stk Work.Layout.sTmp = X Work.Layout.sTmp ∧
      (∀ j, j ≠ Work.Layout.sBit → j ≠ Work.Layout.sD → j ≠ Work.Layout.sDp →
        j ≠ Work.Layout.sTmp → s'.stk j = X j) := by
  -- the binary counter of a positive number starts with a genuine bit, not the frame marker
  obtain ⟨b, t, hbt⟩ : ∃ b t, k.bits = b :: t :=
    List.exists_cons_of_ne_nil (bits_ne_nil_of_pos hk)
  have hbit_head : (X Work.Layout.sBit).headD HvdH.Glyph.eos = HvdH.Glyph.bit b := by
    rw [hbit, hbt]
    simp [Work.Layout.bitsG_x]
  have hbit_ne : (X Work.Layout.sBit).headD HvdH.Glyph.eos ≠ Work.Layout.gMark := by
    rw [hbit_head]
    exact fun h => Work.Layout.gMark_ne_bit b h.symm
  have hD_head : (X Work.Layout.sD).headD HvdH.Glyph.eos = Work.Layout.gU := by
    rw [hD]; exact headD_replicate_gU_append hlen _
  have hD_tail : (X Work.Layout.sD).tail
      = List.replicate (len - 1) Work.Layout.gU ++ Work.Layout.gMark :: Drest := by
    rw [hD]; exact tail_replicate_gU_append hlen _
  -- the three states the two `peek`s and the intermediate `pop` produce
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g Work.Layout.rE_x Work.Layout.gU
  let g2 : HvdH.Reg → HvdH.Glyph := Function.update g1 Work.Layout.rE_x (HvdH.Glyph.bit b)
  let g3 : HvdH.Reg → HvdH.Glyph := Function.update g2 Work.Layout.rE_x Work.Layout.gU
  let X3 : HvdH.Stk → List HvdH.Glyph := Function.update X Work.Layout.sD (X Work.Layout.sD).tail
  have hpeek1 : Work.Layout.Ev main (.peek Work.Layout.sD Work.Layout.rE_x) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main Work.Layout.sD Work.Layout.rE_x g X
    rw [hD_head] at h
    exact h
  have hreg1 : (⟨g1, X⟩ : HvdH.State).reg Work.Layout.rE_x = Work.Layout.gU := by
    show g1 Work.Layout.rE_x = Work.Layout.gU
    simp only [g1, Function.update_self]
  have hpeek2 : Work.Layout.Ev main (.peek Work.Layout.sBit Work.Layout.rE_x) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main Work.Layout.sBit Work.Layout.rE_x g1 X
    rw [hbit_head] at h
    exact h
  have hreg2 : (⟨g2, X⟩ : HvdH.State).reg Work.Layout.rE_x ≠ Work.Layout.gMark := by
    show g2 Work.Layout.rE_x ≠ Work.Layout.gMark
    simp only [g2, Function.update_self]
    exact fun h => Work.Layout.gMark_ne_bit b h.symm
  have hpop : Work.Layout.Ev main (.pop Work.Layout.sD Work.Layout.rE_x) ⟨g2, X⟩ ⟨g3, X3⟩ 1 := by
    have h := ev_pop' main Work.Layout.sD Work.Layout.rE_x g2 X
    rw [hD_head] at h
    exact h
  -- the state on which `decProg` runs
  have hbit3 : X3 Work.Layout.sBit = Work.Layout.bitsG_x k.bits ++ Work.Layout.gMark :: R := by
    simp only [X3, Function.update_of_ne Work.Layout.sBit_ne_sD]
    exact hbit
  have hX3_D : X3 Work.Layout.sD = List.replicate (len - 1) Work.Layout.gU ++ Work.Layout.gMark :: Drest := by
    simp only [X3, Function.update_self]
    exact hD_tail
  have hX3_Dp : X3 Work.Layout.sDp = X Work.Layout.sDp := by
    simp only [X3, Function.update_of_ne Work.Layout.sDp_ne_sD]
  have hX3_Tmp : X3 Work.Layout.sTmp = X Work.Layout.sTmp := by
    simp only [X3, Function.update_of_ne Work.Layout.sTmp_ne_sD]
  have hX3_any : ∀ j, j ≠ Work.Layout.sD → X3 j = X j := by
    intro j hj
    simp only [X3, Function.update_of_ne hj]
  obtain ⟨s4, n4, h4ev, h4cost, h4bit, h4tmp, h4frame⟩ := hdec k R g3 X3 hk hbit3
  -- the final state: `decProg`, then `set rE_x gU`, `push sDp rE_x`, `set rG gCont_x`
  let S7 : HvdH.State :=
    ⟨Function.update (Function.update s4.reg Work.Layout.rE_x Work.Layout.gU) Work.Layout.rG
        Work.Layout.gCont_x,
      Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)⟩
  have hset : Work.Layout.Ev main (.set Work.Layout.rE_x Work.Layout.gU) s4
      ⟨Function.update s4.reg Work.Layout.rE_x Work.Layout.gU, s4.stk⟩ 1 :=
    ev_set' main Work.Layout.rE_x Work.Layout.gU s4.reg s4.stk
  have hpush : Work.Layout.Ev main (.push Work.Layout.sDp Work.Layout.rE_x)
      ⟨Function.update s4.reg Work.Layout.rE_x Work.Layout.gU, s4.stk⟩
      ⟨Function.update s4.reg Work.Layout.rE_x Work.Layout.gU,
        Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)⟩ 1 := by
    have h := ev_push' main Work.Layout.sDp Work.Layout.rE_x
      (Function.update s4.reg Work.Layout.rE_x Work.Layout.gU) s4.stk
    rwa [Function.update_self] at h
  have hsetg : Work.Layout.Ev main (.set Work.Layout.rG Work.Layout.gCont_x)
      ⟨Function.update s4.reg Work.Layout.rE_x Work.Layout.gU,
        Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)⟩ S7 1 :=
    ev_set' main Work.Layout.rG Work.Layout.gCont_x _ _
  have htail3 : Work.Layout.Ev main
      (.seq (.set Work.Layout.rE_x Work.Layout.gU)
        (.seq (.push Work.Layout.sDp Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x)))
      s4 S7 3 :=
    Ev.seq' hset (Ev.seq' hpush hsetg (by rfl)) (by rfl)
  have hdecSeg : Work.Layout.Ev main
      (.seq Work.Layout.decProg
        (.seq (.set Work.Layout.rE_x Work.Layout.gU)
          (.seq (.push Work.Layout.sDp Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x))))
      ⟨g3, X3⟩ S7 (n4 + 3) :=
    Ev.seq' h4ev htail3 (by omega)
  have hbranch2 : Work.Layout.Ev main
      (.seq (.pop Work.Layout.sD Work.Layout.rE_x)
        (.seq Work.Layout.decProg
          (.seq (.set Work.Layout.rE_x Work.Layout.gU)
            (.seq (.push Work.Layout.sDp Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x)))))
      ⟨g2, X⟩ S7 (n4 + 4) :=
    Ev.seq' hpop hdecSeg (by omega)
  have hite2 : Work.Layout.Ev main
      (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG HvdH.Glyph.eos)
        (.seq (.pop Work.Layout.sD Work.Layout.rE_x)
          (.seq Work.Layout.decProg
            (.seq (.set Work.Layout.rE_x Work.Layout.gU)
              (.seq (.push Work.Layout.sDp Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x))))))
      ⟨g2, X⟩ S7 (n4 + 5) :=
    Ev.iteF hreg2 hbranch2
  have hbranch1 : Work.Layout.Ev main
      (.seq (.peek Work.Layout.sBit Work.Layout.rE_x)
        (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG HvdH.Glyph.eos)
          (.seq (.pop Work.Layout.sD Work.Layout.rE_x)
            (.seq Work.Layout.decProg
              (.seq (.set Work.Layout.rE_x Work.Layout.gU)
                (.seq (.push Work.Layout.sDp Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x)))))))
      ⟨g1, X⟩ S7 (n4 + 6) :=
    Ev.seq' hpeek2 hite2 (by omega)
  have hite1 : Work.Layout.Ev main
      (.ite Work.Layout.rE_x Work.Layout.gU
        (.seq (.peek Work.Layout.sBit Work.Layout.rE_x)
          (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG HvdH.Glyph.eos)
            (.seq (.pop Work.Layout.sD Work.Layout.rE_x)
              (.seq Work.Layout.decProg
                (.seq (.set Work.Layout.rE_x Work.Layout.gU)
                  (.seq (.push Work.Layout.sDp Work.Layout.rE_x)
                    (.set Work.Layout.rG Work.Layout.gCont_x)))))))
        (.set Work.Layout.rG HvdH.Glyph.eos))
      ⟨g1, X⟩ S7 (n4 + 7) :=
    Ev.iteT hreg1 hbranch1
  have hbody : Work.Layout.Ev main
      (.seq (.peek Work.Layout.sD Work.Layout.rE_x)
        (.ite Work.Layout.rE_x Work.Layout.gU
          (.seq (.peek Work.Layout.sBit Work.Layout.rE_x)
            (.ite Work.Layout.rE_x Work.Layout.gMark (.set Work.Layout.rG HvdH.Glyph.eos)
              (.seq (.pop Work.Layout.sD Work.Layout.rE_x)
                (.seq Work.Layout.decProg
                  (.seq (.set Work.Layout.rE_x Work.Layout.gU)
                    (.seq (.push Work.Layout.sDp Work.Layout.rE_x)
                      (.set Work.Layout.rG Work.Layout.gCont_x)))))))
          (.set Work.Layout.rG HvdH.Glyph.eos)))
      ⟨g, X⟩ S7 (n4 + 8) :=
    Ev.seq' hpeek1 hite1 (by omega)
  have hmain : Work.Layout.Ev main Work.Layout.cmpBody ⟨g, X⟩ S7 (n4 + 8) := by
    unfold Work.Layout.cmpBody
    exact hbody
  refine ⟨S7, n4 + 8, hmain, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)
        Work.Layout.sBit = Work.Layout.bitsG_x (k - 1).bits ++ Work.Layout.gMark :: R
    rw [Function.update_of_ne Work.Layout.sBit_ne_sDp, h4bit]
  · show Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)
        Work.Layout.sD = List.replicate (len - 1) Work.Layout.gU ++ Work.Layout.gMark :: Drest
    rw [Function.update_of_ne Work.Layout.sD_ne_sDp,
      h4frame Work.Layout.sD Work.Layout.sD_ne_sBit Work.Layout.sD_ne_sTmp, hX3_D]
  · show Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)
        Work.Layout.sDp = Work.Layout.gU :: X Work.Layout.sDp
    rw [Function.update_self,
      h4frame Work.Layout.sDp Work.Layout.sDp_ne_sBit Work.Layout.sDp_ne_sTmp, hX3_Dp]
  · show Function.update (Function.update s4.reg Work.Layout.rE_x Work.Layout.gU) Work.Layout.rG
        Work.Layout.gCont_x Work.Layout.rG = Work.Layout.gCont_x
    rw [Function.update_self]
  · show Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp)
        Work.Layout.sTmp = X Work.Layout.sTmp
    rw [Function.update_of_ne Work.Layout.sTmp_ne_sDp, h4tmp, hX3_Tmp]
  · intro j hjb hjd hjdp hjtmp
    show Function.update s4.stk Work.Layout.sDp (Work.Layout.gU :: s4.stk Work.Layout.sDp) j = X j
    rw [Function.update_of_ne hjdp, h4frame j hjb hjtmp, hX3_any j hjd]

end Work.Layout.Take
