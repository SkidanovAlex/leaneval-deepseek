import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.gcdInvDefs
import Submission.Work.IntLib.SqrtGcd.dup2EvalGen
import Submission.Work.IntLib.SqrtGcd.subDigitsArith
import Submission.Work.IntLib.SqrtGcd.subLoopEvalXU
import Submission.Work.IntLib.SqrtGcd.gcdStepSpec

/-!
# The body of the binary-gcd loop

Same statement as `Work.IntLib.SqrtGcd.gcdBodySpec` (`Submission/Work/IntLib/SqrtGcd/gcdBodySpec.lean`),
with the `gcdTake` specification `gcdTakeSpecMine` proved locally (see `gcdBody2_subDigitsArith` for
the arithmetic of the ripple subtracter and `gb2_moveSameEval` for the region mover).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.IntLib


/-! ## Private helpers -/

private theorem gb2_mk_ne_eos (k : Stk) : Glyph.mk k ≠ Glyph.eos := fun h => by cases h
private theorem gb2_mk_ne_bit (k : Stk) (b : Bool) : Glyph.mk k ≠ Glyph.bit b := fun h => by cases h
private theorem gb2_bit_ne_mk (k : Stk) (b : Bool) : Glyph.bit b ≠ Glyph.mk k :=
  fun h => gb2_mk_ne_bit k b h.symm
private theorem gb2_bit_ne_eos (b : Bool) : Glyph.bit b ≠ Glyph.eos := fun h => by cases h
private theorem gb2_bit_false_ne_true : Glyph.bit false ≠ Glyph.bit true := fun h => by cases h
private theorem gb2_head?_ne {g h : Glyph} {gs : List Glyph} (hgh : g ≠ h) :
    (g :: gs).head? ≠ some h := by
  simp only [List.head?_cons]
  exact fun hh => hgh (Option.some.inj hh)

private theorem gb2_nFalses_le (l : List Bool) : nFalses l ≤ l.length := by
  have h := congrArg List.length (replicate_nFalses_dropFalses l)
  simp only [List.length_append, List.length_replicate] at h
  omega

private theorem gb2_dropFalses_append_true_ne_nil (X : List Bool) :
    dropFalses (X ++ [true]) ≠ [] := by
  induction X with
  | nil => simp [dropFalses]
  | cons b t ih =>
    cases b with
    | true => simp [dropFalses]
    | false => simpa [List.cons_append, dropFalses] using ih

private theorem gb2_mStKP (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h : k ≠ d) : (SG.mSt k T d r gs below s).stk k = T :: below := by
  simp [SG.mSt, h]

private theorem gb2_mStDP (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) : (SG.mSt k T d r gs below s).stk d = gs.reverse ++ s.stk d := by
  simp [SG.mSt]

private theorem gb2_mStOP (k : Stk) (T : Glyph) (d j : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h1 : j ≠ k) (h2 : j ≠ d) : (SG.mSt k T d r gs below s).stk j = s.stk j := by
  simp [SG.mSt, h1, h2]

private theorem gb2_dStK (k : Stk) (T : Glyph) (r : Reg) (below : List Glyph) (s : State) :
    (SG.dSt k T r below s).stk k = T :: below := by simp [SG.dSt]

private theorem gb2_dStO (k : Stk) (T : Glyph) (r : Reg) (below : List Glyph) (s : State)
    {j : Stk} (h : j ≠ k) : (SG.dSt k T r below s).stk j = s.stk j := by simp [SG.dSt, h]

/-- `SG.moveSame src dst tmp r` moves a bit region while preserving its order. -/
private theorem gb2_moveSameEval (main : HvdH.Cmd) (src dst tmp : HvdH.Stk) (r : HvdH.Reg)
    (A : List Bool) (bsrc btmp : List HvdH.Glyph) (s : HvdH.State)
    (hsrc : s.stk src = A.map HvdH.Glyph.bit ++ HvdH.Glyph.mk src :: bsrc)
    (htmp : s.stk tmp = HvdH.Glyph.mk tmp :: btmp)
    (hds : dst ≠ src) (hdt : dst ≠ tmp) (hts : tmp ≠ src) :
    ∃ s' m, HvdH.Eval main (SG.moveSame src dst tmp r) s s' m ∧
      m ≤ 14 + 10 * A.length ∧
      s'.stk src = HvdH.Glyph.mk src :: bsrc ∧
      s'.stk tmp = HvdH.Glyph.mk tmp :: btmp ∧
      s'.stk dst = A.map HvdH.Glyph.bit ++ s.stk dst ∧
      (∀ j : HvdH.Stk, j ≠ src → j ≠ tmp → j ≠ dst → s'.stk j = s.stk j) := by
  let s1 : State := SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s
  let s2 : State := SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1
  have h1 : Eval main (SG.rLoop src (Glyph.mk src) (some tmp) r) s s1
      (7 + (A.map Glyph.bit).length * 5) :=
    SG.mLoop_eval main src (Glyph.mk src) tmp r (gb2_mk_ne_eos src) hts (A.map Glyph.bit) bsrc s
      hsrc (fun g hg => by
        rw [List.mem_map] at hg
        obtain ⟨b, -, hb⟩ := hg
        rw [← hb]; exact gb2_bit_ne_mk src b)
  have ht1 : s1.stk tmp = A.reverse.map Glyph.bit ++ Glyph.mk tmp :: btmp := by
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk tmp = _
    rw [gb2_mStDP, htmp, List.map_reverse]
  have h2 : Eval main (SG.rLoop tmp (Glyph.mk tmp) (some dst) r) s1 s2
      (7 + (A.reverse.map Glyph.bit).length * 5) :=
    SG.mLoop_eval main tmp (Glyph.mk tmp) dst r (gb2_mk_ne_eos tmp) hdt (A.reverse.map Glyph.bit)
      btmp s1 ht1 (fun g hg => by
        rw [List.mem_map] at hg
        obtain ⟨b, -, hb⟩ := hg
        rw [← hb]; exact gb2_bit_ne_mk tmp b)
  have hmv : SG.moveSame src dst tmp r
      = .seq (SG.rLoop src (Glyph.mk src) (some tmp) r)
             (SG.rLoop tmp (Glyph.mk tmp) (some dst) r) := rfl
  refine ⟨s2, (7 + (A.map Glyph.bit).length * 5) + (7 + (A.reverse.map Glyph.bit).length * 5),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmv]; exact Eval.seq h1 h2
  · simp only [List.length_map, List.length_reverse]; omega
  · show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk src
        = Glyph.mk src :: bsrc
    rw [gb2_mStOP tmp (Glyph.mk tmp) dst src r (A.reverse.map Glyph.bit) btmp s1 hts.symm hds.symm]
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk src = Glyph.mk src :: bsrc
    rw [gb2_mStKP src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s hts.symm]
  · show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk tmp
        = Glyph.mk tmp :: btmp
    rw [gb2_mStKP tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1 hdt.symm]
  · have hdst1 : s1.stk dst = s.stk dst := by
      show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk dst = s.stk dst
      rw [gb2_mStOP src (Glyph.mk src) tmp dst r (A.map Glyph.bit) bsrc s hds hdt]
    show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk dst
        = A.map Glyph.bit ++ s.stk dst
    rw [gb2_mStDP tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1, List.map_reverse,
      List.reverse_reverse, hdst1]
  · intro j hjS hjT hjD
    show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk j = s.stk j
    rw [gb2_mStOP tmp (Glyph.mk tmp) dst j r (A.reverse.map Glyph.bit) btmp s1 hjT hjD]
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk j = s.stk j
    rw [gb2_mStOP src (Glyph.mk src) tmp j r (A.map Glyph.bit) bsrc s hjS hjT]


/-! ## The `gcdTake` step: strip the leading zero bits, then take the odd part -/

/-- Specification of `SG.gcdTake dst` (`Submission/Work/IntLib/SqrtGcd/GcdProg.lean`): the region
of `sS` is read most significant bit first; its leading `false` bits are dropped, and if nothing
is left (`bval D = 0`) the loop flag is set to `gStop` and `dst` is left alone, while otherwise
the odd part of `bval D` is written (least significant bit first) on `dst` and the loop flag is set
to `gGo`.  The stacks `sS`, `sP`, `sQ`, `dst` are the only ones touched. -/
theorem gcdTakeSpecMine (main : HvdH.Cmd) (dst : HvdH.Stk) (D A : List Bool)
    (bS bP bQ bdst : List HvdH.Glyph) (s : HvdH.State)
    (hdP : dst ≠ Work.IntLib.SG.sP) (hdQ : dst ≠ Work.IntLib.SG.sQ)
    (hdS : dst ≠ Work.IntLib.SG.sS)
    (hS : s.stk Work.IntLib.SG.sS = D.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sS :: bS)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hD : s.stk dst = A.map HvdH.Glyph.bit ++ HvdH.Glyph.mk dst :: bdst) :
    ∃ s' m, HvdH.Eval main (Work.IntLib.SG.gcdTake dst) s s' m ∧
      m ≤ 40 * (D.length + A.length + 1) + 40 ∧
      s'.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP ∧
      s'.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ ∧
      ((Work.IntLib.SG.bval D = 0 ∧
          s'.stk dst = A.map HvdH.Glyph.bit ++ HvdH.Glyph.mk dst :: bdst ∧
          s'.reg Work.IntLib.SG.rgF = Work.IntLib.SG.gStop) ∨
        (Work.IntLib.SG.bval D ≠ 0 ∧
          (∃ l : List Bool, s'.stk dst = l.map HvdH.Glyph.bit ++ HvdH.Glyph.mk dst :: bdst ∧
            Work.IntLib.ofBits l = Work.IntLib.SG.oddPart (Work.IntLib.SG.bval D) ∧
            l.length ≤ D.length) ∧
          s'.reg Work.IntLib.SG.rgF = Work.IntLib.SG.gGo)) ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.SG.sS → j ≠ Work.IntLib.SG.sP →
        j ≠ Work.IntLib.SG.sQ → j ≠ dst → s'.stk j = s.stk j) := by
  have hDmap : D.map Glyph.bit = (List.replicate (nFalses D) false).map Glyph.bit
      ++ (dropFalses D).map Glyph.bit := by
    conv_lhs => rw [← replicate_nFalses_dropFalses D]
    rw [List.map_append]
  have hS1 : s.stk SG.sS = (List.replicate (nFalses D) false).map Glyph.bit
      ++ ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) := by
    rw [hS, hDmap, List.append_assoc]
  have hnl : nFalses D ≤ D.length := gb2_nFalses_le D
  rcases dropFalses_eq_nil_or_head_true D with hR0 | ⟨l', hRc⟩
  · -- #### the all-`false` case: `bval D = 0`
    have hrest : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).head?
        ≠ some (Glyph.bit false) := by
      rw [hR0, List.map_nil, List.nil_append]
      exact gb2_head?_ne (gb2_mk_ne_bit SG.sS false)
    have heos : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).head?
        ≠ some Glyph.eos := by
      rw [hR0, List.map_nil, List.nil_append]
      exact gb2_head?_ne (gb2_mk_ne_eos SG.sS)
    have hhd1 : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).headD Glyph.eos
        = Glyph.mk SG.sS := by
      rw [hR0, List.map_nil, List.nil_append]
      rfl
    have hst1 : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS)
        = Glyph.mk SG.sS :: bS := by
      rw [hR0, List.map_nil, List.nil_append]
    have hev1 := SG.stripZeros_eval main SG.sS SG.rgT (nFalses D)
      ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) s hS1 hrest heos
    rw [hhd1, hst1] at hev1
    set s1 : State := ⟨Function.update s.reg SG.rgT (Glyph.mk SG.sS),
        Function.update s.stk SG.sS (Glyph.mk SG.sS :: bS)⟩ with hs1def
    have hev1' : Eval main (SG.stripZeros SG.sS SG.rgT) s s1 (2 * nFalses D + 6) := hev1
    have hs1S : s1.stk SG.sS = Glyph.mk SG.sS :: bS := by simp [hs1def]
    have hs1T : s1.reg SG.rgT = Glyph.mk SG.sS := by simp [hs1def]
    have hs1P : s1.stk SG.sP = Glyph.mk SG.sP :: bP := by
      show Function.update s.stk SG.sS (Glyph.mk SG.sS :: bS) SG.sP = Glyph.mk SG.sP :: bP
      rw [Function.update_of_ne (by decide : SG.sP ≠ SG.sS)]
      exact hP
    have hs1Q : s1.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      show Function.update s.stk SG.sS (Glyph.mk SG.sS :: bS) SG.sQ = Glyph.mk SG.sQ :: bQ
      rw [Function.update_of_ne (by decide : SG.sQ ≠ SG.sS)]
      exact hQ
    have hs1D : s1.stk dst = A.map Glyph.bit ++ Glyph.mk dst :: bdst := by
      show Function.update s.stk SG.sS (Glyph.mk SG.sS :: bS) dst
        = A.map Glyph.bit ++ Glyph.mk dst :: bdst
      rw [Function.update_of_ne hdS]
      exact hD
    have hev2 : Eval main (.peek SG.sS SG.rgT) s1 s1 1 := by
      have h := Eval.peek (main := main) SG.sS SG.rgT s1
      have hhead : (s1.stk SG.sS).headD Glyph.eos = s1.reg SG.rgT := by rw [hs1S, hs1T]; rfl
      rw [hhead, Function.update_eq_self] at h
      exact h
    have hev3 : Eval main (.ite SG.rgT (Glyph.mk SG.sS) (.set SG.rgF SG.gStop)
        (Work.Layout.seqs [ SG.rLoop SG.sS (Glyph.mk SG.sS) (some SG.sP) SG.rgT,
          SG.stripZeros SG.sP SG.rgT, SG.rLoop dst (Glyph.mk dst) none SG.rgT,
          SG.moveSame SG.sP dst SG.sQ SG.rgT, .set SG.rgF SG.gGo ]))
        s1 ⟨Function.update s1.reg SG.rgF SG.gStop, s1.stk⟩ 2 :=
      Eval.iteT hs1T (Eval.set SG.rgF SG.gStop s1)
    refine ⟨⟨Function.update s1.reg SG.rgF SG.gStop, s1.stk⟩, (2 * nFalses D + 6) + (1 + 2),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Eval.seq hev1' (Eval.seq hev2 hev3)
    · omega
    · show s1.stk SG.sS = Glyph.mk SG.sS :: bS; exact hs1S
    · show s1.stk SG.sP = Glyph.mk SG.sP :: bP; exact hs1P
    · show s1.stk SG.sQ = Glyph.mk SG.sQ :: bQ; exact hs1Q
    · refine Or.inl ⟨(bval_eq_zero_iff D).mpr hR0, ?_, rfl⟩
      show s1.stk dst = A.map Glyph.bit ++ Glyph.mk dst :: bdst
      exact hs1D
    · intro j hjS hjP hjQ hjD
      show Function.update s.stk SG.sS (Glyph.mk SG.sS :: bS) j = s.stk j
      rw [Function.update_of_ne hjS]
  · -- #### the non-zero case: `bval D ≠ 0`
    have hRrev : (dropFalses D).reverse = l'.reverse ++ [true] := by rw [hRc, List.reverse_cons]
    have hrest : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).head?
        ≠ some (Glyph.bit false) := by
      rw [hRc, List.map_cons, List.cons_append]
      exact gb2_head?_ne (gb2_bit_false_ne_true.symm)
    have heos : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).head?
        ≠ some Glyph.eos := by
      rw [hRc, List.map_cons, List.cons_append]
      exact gb2_head?_ne (gb2_bit_ne_eos true)
    have hhd1 : ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS).headD Glyph.eos
        = Glyph.bit true := by
      rw [hRc, List.map_cons, List.cons_append]
      rfl
    have hev1 := SG.stripZeros_eval main SG.sS SG.rgT (nFalses D)
      ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) s hS1 hrest heos
    rw [hhd1] at hev1
    set s1 : State := ⟨Function.update s.reg SG.rgT (Glyph.bit true),
        Function.update s.stk SG.sS ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS)⟩
      with hs1def
    have hev1' : Eval main (SG.stripZeros SG.sS SG.rgT) s s1 (2 * nFalses D + 6) := hev1
    have hs1S : s1.stk SG.sS = (dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS := by
      simp [hs1def]
    have hs1T : s1.reg SG.rgT = Glyph.bit true := by simp [hs1def]
    have hs1P : s1.stk SG.sP = Glyph.mk SG.sP :: bP := by
      show Function.update s.stk SG.sS
          ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) SG.sP = Glyph.mk SG.sP :: bP
      rw [Function.update_of_ne (by decide : SG.sP ≠ SG.sS)]
      exact hP
    have hs1Q : s1.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      show Function.update s.stk SG.sS
          ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) SG.sQ = Glyph.mk SG.sQ :: bQ
      rw [Function.update_of_ne (by decide : SG.sQ ≠ SG.sS)]
      exact hQ
    have hs1D : s1.stk dst = A.map Glyph.bit ++ Glyph.mk dst :: bdst := by
      show Function.update s.stk SG.sS
          ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) dst
        = A.map Glyph.bit ++ Glyph.mk dst :: bdst
      rw [Function.update_of_ne hdS]
      exact hD
    have hs1T' : s1.reg SG.rgT ≠ Glyph.mk SG.sS := by rw [hs1T]; exact gb2_bit_ne_mk SG.sS true
    have hev2 : Eval main (.peek SG.sS SG.rgT) s1 s1 1 := by
      have h := Eval.peek (main := main) SG.sS SG.rgT s1
      have hhead : (s1.stk SG.sS).headD Glyph.eos = s1.reg SG.rgT := by
        rw [hs1S, hs1T, hRc, List.map_cons, List.cons_append]; rfl
      rw [hhead, Function.update_eq_self] at h
      exact h
    -- the inner sequence: rLoop sS -> sP, stripZeros sP, rLoop dst -> none, moveSame sP -> dst
    have hmem1 : ∀ g ∈ (dropFalses D).map Glyph.bit, g ≠ Glyph.mk SG.sS := by
      intro g hg; rw [List.mem_map] at hg; obtain ⟨b, -, hb⟩ := hg
      rw [← hb]; exact gb2_bit_ne_mk SG.sS b
    have hevb1 : Eval main (SG.rLoop SG.sS (Glyph.mk SG.sS) (some SG.sP) SG.rgT) s1
        (SG.mSt SG.sS (Glyph.mk SG.sS) SG.sP SG.rgT ((dropFalses D).map Glyph.bit) bS s1)
        (7 + ((dropFalses D).map Glyph.bit).length * 5) :=
      SG.mLoop_eval main SG.sS (Glyph.mk SG.sS) SG.sP SG.rgT (gb2_mk_ne_eos SG.sS) (by decide)
        ((dropFalses D).map Glyph.bit) bS s1 hs1S hmem1
    set s2 : State := SG.mSt SG.sS (Glyph.mk SG.sS) SG.sP SG.rgT
      ((dropFalses D).map Glyph.bit) bS s1 with hs2def
    have hevb1' : Eval main (SG.rLoop SG.sS (Glyph.mk SG.sS) (some SG.sP) SG.rgT) s1 s2
        (7 + ((dropFalses D).map Glyph.bit).length * 5) := hevb1
    have hs2S : s2.stk SG.sS = Glyph.mk SG.sS :: bS := by
      rw [hs2def]; exact gb2_mStKP SG.sS (Glyph.mk SG.sS) SG.sP SG.rgT
        ((dropFalses D).map Glyph.bit) bS s1 (by decide)
    have hs2P : s2.stk SG.sP = ((dropFalses D).reverse).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP := by
      rw [hs2def, gb2_mStDP, hs1P, List.map_reverse]
    have hs2Q : s2.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      rw [hs2def, gb2_mStOP SG.sS (Glyph.mk SG.sS) SG.sP SG.sQ SG.rgT
        ((dropFalses D).map Glyph.bit) bS s1 (by decide) (by decide), hs1Q]
    have hs2D : s2.stk dst = A.map Glyph.bit ++ Glyph.mk dst :: bdst := by
      rw [hs2def, gb2_mStOP SG.sS (Glyph.mk SG.sS) SG.sP dst SG.rgT
        ((dropFalses D).map Glyph.bit) bS s1 hdS hdP, hs1D]
    -- stripZeros on sP
    have hmap2 : ((dropFalses D).reverse).map Glyph.bit
        = (List.replicate (nFalses ((dropFalses D).reverse)) false).map Glyph.bit
          ++ (dropFalses ((dropFalses D).reverse)).map Glyph.bit := by
      conv_lhs => rw [← replicate_nFalses_dropFalses ((dropFalses D).reverse)]
      rw [List.map_append]
    have hS2 : s2.stk SG.sP = (List.replicate (nFalses ((dropFalses D).reverse)) false).map Glyph.bit
        ++ ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) := by
      rw [hs2P, hmap2, List.append_assoc]
    have hlne : dropFalses ((dropFalses D).reverse) ≠ [] := by
      have h := gb2_dropFalses_append_true_ne_nil l'.reverse
      rwa [← hRrev] at h
    have hlshape : ∃ l'', dropFalses ((dropFalses D).reverse) = true :: l'' := by
      rcases dropFalses_eq_nil_or_head_true ((dropFalses D).reverse) with h | h
      · exact absurd h hlne
      · exact h
    have hrest2 : ((dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP).head? ≠ some (Glyph.bit false) := by
      obtain ⟨l'', hl''⟩ := hlshape
      rw [hl'', List.map_cons, List.cons_append]
      exact gb2_head?_ne (gb2_bit_false_ne_true.symm)
    have heos2 : ((dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP).head? ≠ some Glyph.eos := by
      obtain ⟨l'', hl''⟩ := hlshape
      rw [hl'', List.map_cons, List.cons_append]
      exact gb2_head?_ne (gb2_bit_ne_eos true)
    have hhd2 : ((dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP).headD Glyph.eos = Glyph.bit true := by
      obtain ⟨l'', hl''⟩ := hlshape
      rw [hl'', List.map_cons, List.cons_append]
      rfl
    have hevb2 := SG.stripZeros_eval main SG.sP SG.rgT (nFalses ((dropFalses D).reverse))
      ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) s2 hS2 hrest2 heos2
    rw [hhd2] at hevb2
    set s3 : State := ⟨Function.update s2.reg SG.rgT (Glyph.bit true),
        Function.update s2.stk SG.sP
          ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP)⟩
      with hs3def
    have hevb2' : Eval main (SG.stripZeros SG.sP SG.rgT) s2 s3
        (2 * nFalses ((dropFalses D).reverse) + 6) := hevb2
    have hs3P : s3.stk SG.sP = (dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP := by simp [hs3def]
    have hs3S : s3.stk SG.sS = Glyph.mk SG.sS :: bS := by
      show Function.update s2.stk SG.sP
          ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) SG.sS
        = Glyph.mk SG.sS :: bS
      rw [Function.update_of_ne (by decide : SG.sS ≠ SG.sP)]
      exact hs2S
    have hs3Q : s3.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      show Function.update s2.stk SG.sP
          ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) SG.sQ
        = Glyph.mk SG.sQ :: bQ
      rw [Function.update_of_ne (by decide : SG.sQ ≠ SG.sP)]
      exact hs2Q
    have hs3D : s3.stk dst = A.map Glyph.bit ++ Glyph.mk dst :: bdst := by
      show Function.update s2.stk SG.sP
          ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) dst
        = A.map Glyph.bit ++ Glyph.mk dst :: bdst
      rw [Function.update_of_ne hdP]
      exact hs2D
    -- drop the region of dst
    have hmem3 : ∀ g ∈ A.map Glyph.bit, g ≠ Glyph.mk dst := by
      intro g hg; rw [List.mem_map] at hg; obtain ⟨b, -, hb⟩ := hg
      rw [← hb]; exact gb2_bit_ne_mk dst b
    have hevb3 : Eval main (SG.rLoop dst (Glyph.mk dst) none SG.rgT) s3
        (SG.dSt dst (Glyph.mk dst) SG.rgT bdst s3) (7 + (A.map Glyph.bit).length * 5) :=
      SG.dLoop_eval main dst (Glyph.mk dst) SG.rgT (gb2_mk_ne_eos dst) (A.map Glyph.bit) bdst s3
        hs3D hmem3
    set s4 : State := SG.dSt dst (Glyph.mk dst) SG.rgT bdst s3 with hs4def
    have hevb3' : Eval main (SG.rLoop dst (Glyph.mk dst) none SG.rgT) s3 s4
        (7 + (A.map Glyph.bit).length * 5) := hevb3
    have hs4D : s4.stk dst = Glyph.mk dst :: bdst := by
      rw [hs4def]; exact gb2_dStK dst (Glyph.mk dst) SG.rgT bdst s3
    have hs4S : s4.stk SG.sS = Glyph.mk SG.sS :: bS := by
      rw [hs4def, gb2_dStO dst (Glyph.mk dst) SG.rgT bdst s3 hdS.symm]; exact hs3S
    have hs4P : s4.stk SG.sP = (dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk SG.sP :: bP := by
      rw [hs4def, gb2_dStO dst (Glyph.mk dst) SG.rgT bdst s3 hdP.symm]; exact hs3P
    have hs4Q : s4.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      rw [hs4def, gb2_dStO dst (Glyph.mk dst) SG.rgT bdst s3 hdQ.symm]; exact hs3Q
    -- move the odd part onto dst
    obtain ⟨s5, m5, hevb4, hm5, hs5P, hs5Q, hs5D, hs5fr⟩ :=
      gb2_moveSameEval main SG.sP dst SG.sQ SG.rgT (dropFalses ((dropFalses D).reverse)) bP bQ s4
        hs4P hs4Q hdP hdQ (by decide)
    have hs5D' : s5.stk dst = (dropFalses ((dropFalses D).reverse)).map Glyph.bit
        ++ Glyph.mk dst :: bdst := by rw [hs5D, hs4D]
    have hs5S : s5.stk SG.sS = Glyph.mk SG.sS :: bS :=
      (hs5fr SG.sS (by decide) (by decide) hdS.symm).trans hs4S
    -- assemble the inner sequence
    have hevb4' : Eval main (SG.moveSame SG.sP dst SG.sQ SG.rgT) s4 s5 m5 := hevb4
    have hevb5 : Eval main (.set SG.rgF SG.gGo) s5
        ⟨Function.update s5.reg SG.rgF SG.gGo, s5.stk⟩ 1 := Eval.set SG.rgF SG.gGo s5
    have hevInner : Eval main
        (Work.Layout.seqs [ SG.rLoop SG.sS (Glyph.mk SG.sS) (some SG.sP) SG.rgT,
          SG.stripZeros SG.sP SG.rgT, SG.rLoop dst (Glyph.mk dst) none SG.rgT,
          SG.moveSame SG.sP dst SG.sQ SG.rgT, .set SG.rgF SG.gGo ]) s1
        ⟨Function.update s5.reg SG.rgF SG.gGo, s5.stk⟩
        ((7 + ((dropFalses D).map Glyph.bit).length * 5)
          + ((2 * nFalses ((dropFalses D).reverse) + 6)
            + ((7 + (A.map Glyph.bit).length * 5) + (m5 + 1)))) :=
      Eval.seq hevb1' (Eval.seq hevb2' (Eval.seq hevb3' (Eval.seq hevb4' hevb5)))
    have hevIte : Eval main (.ite SG.rgT (Glyph.mk SG.sS) (.set SG.rgF SG.gStop)
        (Work.Layout.seqs [ SG.rLoop SG.sS (Glyph.mk SG.sS) (some SG.sP) SG.rgT,
          SG.stripZeros SG.sP SG.rgT, SG.rLoop dst (Glyph.mk dst) none SG.rgT,
          SG.moveSame SG.sP dst SG.sQ SG.rgT, .set SG.rgF SG.gGo ])) s1
        ⟨Function.update s5.reg SG.rgF SG.gGo, s5.stk⟩
        (((7 + ((dropFalses D).map Glyph.bit).length * 5)
          + ((2 * nFalses ((dropFalses D).reverse) + 6)
            + ((7 + (A.map Glyph.bit).length * 5) + (m5 + 1)))) + 1) :=
      Eval.iteF hs1T' hevInner
    have hevTot : Eval main (SG.gcdTake dst) s ⟨Function.update s5.reg SG.rgF SG.gGo, s5.stk⟩
        ((2 * nFalses D + 6) + (1 + (((7 + ((dropFalses D).map Glyph.bit).length * 5)
          + ((2 * nFalses ((dropFalses D).reverse) + 6)
            + ((7 + (A.map Glyph.bit).length * 5) + (m5 + 1)))) + 1))) :=
      Eval.seq hev1' (Eval.seq hev2 hevIte)
    refine ⟨⟨Function.update s5.reg SG.rgF SG.gGo, s5.stk⟩,
      (2 * nFalses D + 6) + (1 + (((7 + ((dropFalses D).map Glyph.bit).length * 5)
        + ((2 * nFalses ((dropFalses D).reverse) + 6)
          + ((7 + (A.map Glyph.bit).length * 5) + (m5 + 1)))) + 1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hevTot
    · have h1 : ((dropFalses D).map Glyph.bit).length = (dropFalses D).length := List.length_map ..
      have h3 : (A.map Glyph.bit).length = A.length := List.length_map ..
      have hl1 : (dropFalses D).length ≤ D.length := length_dropFalses_le D
      have hl2 : (dropFalses ((dropFalses D).reverse)).length ≤ D.length := by
        have h := length_dropFalses_le ((dropFalses D).reverse)
        simp only [List.length_reverse] at h
        omega
      have hzs2 : nFalses ((dropFalses D).reverse) ≤ D.length := by
        have h := gb2_nFalses_le ((dropFalses D).reverse)
        simp only [List.length_reverse] at h
        omega
      have hm5' : m5 ≤ 14 + 10 * (dropFalses ((dropFalses D).reverse)).length := hm5
      rw [h1, h3]
      omega
    · show s5.stk SG.sS = Glyph.mk SG.sS :: bS; exact hs5S
    · show s5.stk SG.sP = Glyph.mk SG.sP :: bP; exact hs5P
    · show s5.stk SG.sQ = Glyph.mk SG.sQ :: bQ; exact hs5Q
    · refine Or.inr ⟨?_, ⟨dropFalses ((dropFalses D).reverse), ?_, ?_, ?_⟩, rfl⟩
      · have hb : SG.bval (dropFalses D) = SG.bval D := bval_dropFalses D
        rw [← hb, hRc, SG.bval_cons]
        simp only [Bool.toNat_true, mul_one]
        have hp : 0 < 2 ^ l'.length := pow_pos (by norm_num) _
        omega
      · show s5.stk dst = _
        exact hs5D'
      · rw [ofBits_dropFalses]
        exact congrArg SG.oddPart (bval_dropFalses D)
      · calc (dropFalses ((dropFalses D).reverse)).length
            ≤ ((dropFalses D).reverse).length := length_dropFalses_le _
          _ = (dropFalses D).length := List.length_reverse ..
          _ ≤ D.length := length_dropFalses_le D
    · intro j hjS hjP hjQ hjD
      show s5.stk j = s.stk j
      have h54 : s5.stk j = s4.stk j := hs5fr j hjP hjQ hjD
      have h43 : s4.stk j = s3.stk j := by
        rw [hs4def]; exact gb2_dStO dst (Glyph.mk dst) SG.rgT bdst s3 hjD
      have h32 : s3.stk j = s2.stk j := by
        show Function.update s2.stk SG.sP
            ((dropFalses ((dropFalses D).reverse)).map Glyph.bit ++ Glyph.mk SG.sP :: bP) j
          = s2.stk j
        rw [Function.update_of_ne hjP]
      have h21 : s2.stk j = s1.stk j := by
        rw [hs2def]; exact gb2_mStOP SG.sS (Glyph.mk SG.sS) SG.sP j SG.rgT
          ((dropFalses D).map Glyph.bit) bS s1 hjS hjP
      have h10 : s1.stk j = s.stk j := by
        show Function.update s.stk SG.sS
            ((dropFalses D).map Glyph.bit ++ Glyph.mk SG.sS :: bS) j = s.stk j
        rw [Function.update_of_ne hjS]
      exact h54.trans (h43.trans (h32.trans (h21.trans h10)))

/-! ## Helper lemmas -/

theorem gcdBody2_mk_ne_eos (k : Stk) : Glyph.mk k ≠ Glyph.eos := fun h => by cases h

theorem gcdBody2_mk_ne_bit (k : Stk) (b : Bool) : Glyph.mk k ≠ Glyph.bit b := fun h => by cases h

theorem gcdBody2_bit_ne_mk (k : Stk) (b : Bool) : Glyph.bit b ≠ Glyph.mk k :=
  fun h => gcdBody2_mk_ne_bit k b h.symm

theorem gcdBody2_bit_false_ne_true : Glyph.bit false ≠ Glyph.bit true := fun h => by cases h

/-- A `set` of the value the register already holds does nothing. -/
theorem gcdBody2_ev_set_self (main : Cmd) (r : Reg) (c : Glyph) (s : State) (h : s.reg r = c) :
    Eval main (.set r c) s s 1 := by
  have h' := Eval.set (main := main) r c s
  have hst : (⟨Function.update s.reg r c, s.stk⟩ : State) = s := by
    apply SG.State.ext'
    · intro q
      simp only [Function.update_apply]
      by_cases hq : q = r
      · subst hq; simp [h]
      · simp [hq]
    · intro q; rfl
  rwa [hst] at h'

/-- `padTo n l` has length `n` when `l` is short enough. -/
theorem gcdBody2_padTo_length (n : ℕ) (l : List Bool) (h : l.length ≤ n) :
    (SG.padTo n l).length = n := by
  rw [SG.padTo, List.length_append, List.length_take, List.length_replicate]
  omega

/-- `bval` of a reversed bit list is the least-significant-first value. -/
theorem gcdBody2_bval_reverse (l : List Bool) : SG.bval l.reverse = ofBits l := by
  simp [SG.bval]

/-- The arithmetic of the ripple subtraction `u - v` at the bit level: which borrow comes out,
what the digits are worth, and when they vanish. -/
theorem gcdBody2_subDigitsArith (u v n : ℕ) (ul vl : List Bool)
    (hn : n = max ul.length vl.length) (hu : ofBits ul = u) (hv : ofBits vl = v) :
    let r := SG.subDigits n ul vl false
    ((r.1 = true ↔ u < v) ∧ (r.1 = false → ofBits r.2 = u - v) ∧
      (ofBits r.2 = 0 ↔ u = v) ∧ r.2.length = n) := by
  have hlen1 : ul.length ≤ n := by rw [hn]; exact Nat.le_max_left _ _
  have hlen2 : vl.length ≤ n := by rw [hn]; exact Nat.le_max_right _ _
  have hp1 : ofBits (SG.padTo n ul) = u := by rw [ofBits_padTo_of_le n ul hlen1, hu]
  have hp2 : ofBits (SG.padTo n vl) = v := by rw [ofBits_padTo_of_le n vl hlen2, hv]
  have hlt : (SG.subDigits n ul vl false).1 = true ↔ u < v := by
    rw [subDigitsArith.1 n ul vl, hp1, hp2]
  have hfalse : (SG.subDigits n ul vl false).1 = false →
      ofBits (SG.subDigits n ul vl false).2 = u - v := by
    intro hf
    rw [subDigitsArith.2.1 n ul vl hf, hp1, hp2]
  have hzero : ofBits (SG.subDigits n ul vl false).2 = 0 ↔ u = v := by
    constructor
    · intro h0
      by_cases hc : (SG.subDigits n ul vl false).1 = true
      · exfalso
        have hspec := subDigitsSpec n ul vl false
        rw [hc] at hspec
        simp only [Bool.toNat_true, mul_one, Bool.toNat_false, add_zero] at hspec
        have hlt2 : v < 2 ^ n := by
          have h3 := ofBits_lt_two_pow (SG.padTo n vl)
          rw [gcdBody2_padTo_length n vl hlen2, hp2] at h3
          exact h3
        rw [hp1, hp2, h0] at hspec
        omega
      · have hf : (SG.subDigits n ul vl false).1 = false := by
          cases hh : (SG.subDigits n ul vl false).1 with
          | false => rfl
          | true => exact absurd hh hc
        have hnotu : ¬ u < v := fun h => hc (hlt.mpr h)
        have h1 : u - v = 0 := by have h2 := hfalse hf; omega
        omega
    · intro huv
      have hf : (SG.subDigits n ul vl false).1 = false := by
        cases hh : (SG.subDigits n ul vl false).1 with
        | false => rfl
        | true => exact absurd (hlt.mp hh) (by omega)
      rw [hfalse hf, huv, Nat.sub_self]
  exact ⟨hlt, hfalse, hzero, subDigitsArith.2.2.2 n ul vl false⟩

/-! ## The specification of the loop body -/

theorem gcdBodySpec2 (main : HvdH.Cmd) (N : ℕ) (bU bV bP bQ bR bS : List HvdH.Glyph)
    (s₀ s : HvdH.State) (u v : ℕ)
    (hs : Work.IntLib.SqrtGcd.GSt N bU bV bP bQ bR bS s₀ s u v)
    (hF : s.reg Work.IntLib.SG.rgF = Work.IntLib.SG.gGo) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.gcdBody s s' m ∧ m ≤ 5000 * (N + 1) ∧
      s'.reg Work.IntLib.SG.rgF = (if u = v then Work.IntLib.SG.gStop else Work.IntLib.SG.gGo) ∧
      Work.IntLib.SqrtGcd.GSt N bU bV bP bQ bR bS s₀ s'
        (Work.IntLib.SqrtGcd.gNext u v).1 (Work.IntLib.SqrtGcd.gNext u v).2 := by
  obtain ⟨ul, hUbits, hUval, hUlen⟩ := hs.hU
  obtain ⟨vl, hVbits, hVval, hVlen⟩ := hs.hV
  have hP0 : s.stk SG.sP = Glyph.mk SG.sP :: bP := hs.hP
  have hQ0 : s.stk SG.sQ = Glyph.mk SG.sQ :: bQ := hs.hQ
  have hR0 : s.stk SG.sR = Glyph.mk SG.sR :: bR := hs.hR
  have hS0 : s.stk SG.sS = Glyph.mk SG.sS :: bS := hs.hS
  -- the arithmetic of the ripple subtraction
  obtain ⟨hAr1, hAr2, hAr3, hAr4⟩ :=
    gcdBody2_subDigitsArith u v (max ul.length vl.length) ul vl rfl hUval hVval
  -- ## 1. set the flag (it is already `gGo`)
  have hEv1 : Work.Layout.Ev main (.set SG.rgF SG.gGo) s s 1 :=
    ⟨1, gcdBody2_ev_set_self main SG.rgF SG.gGo s hF, le_rfl⟩
  -- ## 2. copy `u` onto `sP`
  obtain ⟨s2, m2, hev2, hm2, hs2U, hs2P, hs2R, hs2S, hs2fr⟩ :=
    dup2EvalGen main SG.sU SG.sP SG.sR SG.sS SG.rgT ul bU bP bR bS s hUbits hP0 hR0 hS0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hEv2 : Work.Layout.Ev main (SG.dup2 SG.sU SG.sP SG.sR SG.sS SG.rgT) s s2
      (100 + ul.length * 40) := ⟨m2, hev2, hm2⟩
  have hs2V : s2.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
    rw [hs2fr SG.sV (by decide) (by decide) (by decide) (by decide)]; exact hVbits
  have hs2Q : s2.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
    rw [hs2fr SG.sQ (by decide) (by decide) (by decide) (by decide)]; exact hQ0
  have hs2G : s2.stk SG.sG = s₀.stk SG.sG := by
    rw [hs2fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs.hG
  -- ## 3. copy `v` onto `sQ`
  obtain ⟨s3, m3, hev3, hm3, hs3V, hs3Q, hs3R, hs3S, hs3fr⟩ :=
    dup2EvalGen main SG.sV SG.sQ SG.sR SG.sS SG.rgT vl bV bQ bR bS s2 hs2V hs2Q hs2R hs2S
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hEv3 : Work.Layout.Ev main (SG.dup2 SG.sV SG.sQ SG.sR SG.sS SG.rgT) s2 s3
      (100 + vl.length * 40) := ⟨m3, hev3, hm3⟩
  have hs3P : s3.stk SG.sP = ul.map Glyph.bit ++ Glyph.mk SG.sP :: bP := by
    rw [hs3fr SG.sP (by decide) (by decide) (by decide) (by decide)]; exact hs2P
  have hs3U : s3.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
    rw [hs3fr SG.sU (by decide) (by decide) (by decide) (by decide)]; exact hs2U
  have hs3G : s3.stk SG.sG = s₀.stk SG.sG := by
    rw [hs3fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs2G
  -- ## 4. ripple-subtract `sP - sQ` into `sS`
  obtain ⟨s4, m4, hev4, hm4, hs4P, hs4Q, hs4S, hs4C, hs4fr⟩ :=
    SGX.subLoopEvalXU main SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS
      SG.rgX SG.rgY SG.rgC SG.rgZ SG.rgT SG.rgU SG.rgW ul vl bP bQ s3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (gcdBody2_mk_ne_eos SG.sP) (gcdBody2_mk_ne_eos SG.sQ)
      (fun c => gcdBody2_mk_ne_bit SG.sP c) (fun c => gcdBody2_mk_ne_bit SG.sQ c) hs3P hs3Q
  have hEv4 : Work.Layout.Ev main
      (SG.subLoop SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS
        SG.rgX SG.rgY SG.rgC SG.rgZ SG.rgT SG.rgU SG.rgW) s3 s4
      (40 * (max ul.length vl.length + 1) + 4) := ⟨m4, hev4, hm4⟩
  have hs4Sr : s4.stk SG.sS =
      ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map Glyph.bit
        ++ Glyph.mk SG.sS :: bS := by
    rw [hs4S, hs3S]
  have hs4U : s4.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
    rw [hs4fr SG.sU (by decide) (by decide) (by decide)]; exact hs3U
  have hs4V : s4.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
    rw [hs4fr SG.sV (by decide) (by decide) (by decide)]; exact hs3V
  have hs4R : s4.stk SG.sR = Glyph.mk SG.sR :: bR := by
    rw [hs4fr SG.sR (by decide) (by decide) (by decide)]; exact hs3R
  have hs4G : s4.stk SG.sG = s₀.stk SG.sG := by
    rw [hs4fr SG.sG (by decide) (by decide) (by decide)]; exact hs3G
  -- ## 5. remember the borrow in `rgS1`
  let s5 : State := ⟨Function.update s4.reg SG.rgS1 (s4.reg SG.rgC), s4.stk⟩
  have hEv5 : Work.Layout.Ev main (.mov SG.rgS1 SG.rgC) s4 s5 1 :=
    ⟨1, Eval.mov SG.rgS1 SG.rgC s4, le_rfl⟩
  have hs5S1 : s5.reg SG.rgS1
      = Glyph.bit (SG.subDigits (max ul.length vl.length) ul vl false).1 := by
    simp [s5, hs4C, Function.update_apply]
  have hs5S : s5.stk SG.sS =
      ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map Glyph.bit
        ++ Glyph.mk SG.sS :: bS := hs4Sr
  have hs5P : s5.stk SG.sP = Glyph.mk SG.sP :: bP := hs4P
  have hs5Q : s5.stk SG.sQ = Glyph.mk SG.sQ :: bQ := hs4Q
  have hs5R : s5.stk SG.sR = Glyph.mk SG.sR :: bR := hs4R
  have hs5U : s5.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := hs4U
  have hs5V : s5.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := hs4V
  have hs5G : s5.stk SG.sG = s₀.stk SG.sG := hs4G
  have hs5fr : ∀ j : Stk, j ≠ SG.sU → j ≠ SG.sV → j ≠ SG.sP → j ≠ SG.sQ → j ≠ SG.sR →
      j ≠ SG.sS → s5.stk j = s.stk j := by
    intro j h1 h2 h3 h4 h5 h6
    show s4.stk j = s.stk j
    rw [hs4fr j h3 h4 h6, hs3fr j h2 h4 h5 h6, hs2fr j h1 h3 h5 h6]
  -- ## 6. branch on the borrow
  by_cases hbw : (SG.subDigits (max ul.length vl.length) ul vl false).1 = true
  · -- ### `u < v`: drop `sS`, subtract in the other order, `gcdTake sV`
    have hlt : u < v := hAr1.mp hbw
    have hneS1 : s5.reg SG.rgS1 = Glyph.bit true := by rw [hs5S1, hbw]
    -- 6a. drop the digits on `sS`
    have hstep6 : HvdH.Eval main (SG.rLoop SG.sS (Glyph.mk SG.sS) none SG.rgT) s5
        (SG.dSt SG.sS (Glyph.mk SG.sS) SG.rgT bS s5)
        (7 + (((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map
          Glyph.bit).length * 5) :=
      SG.dLoop_eval main SG.sS (Glyph.mk SG.sS) SG.rgT (gcdBody2_mk_ne_eos SG.sS)
        (((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map Glyph.bit) bS s5
        hs5S (by
          intro g hg
          rw [List.mem_map] at hg
          obtain ⟨b, -, hb⟩ := hg
          rw [← hb]
          exact gcdBody2_bit_ne_mk SG.sS b)
    have hm6 : 7 + (((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map
          Glyph.bit).length * 5 ≤ 7 + max ul.length vl.length * 5 := by
      have h : (((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map
          Glyph.bit).length = max ul.length vl.length := by
        rw [List.length_map, List.length_reverse, hAr4]
      omega
    let s6 : State := SG.dSt SG.sS (Glyph.mk SG.sS) SG.rgT bS s5
    have hEv6a : Work.Layout.Ev main (SG.rLoop SG.sS (Glyph.mk SG.sS) none SG.rgT) s5 s6
        (7 + (((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).map
          Glyph.bit).length * 5) := ⟨_, hstep6, le_rfl⟩
    have hs6S : s6.stk SG.sS = Glyph.mk SG.sS :: bS := by simp [s6, SG.dSt]
    have hs6o : ∀ j : Stk, j ≠ SG.sS → s6.stk j = s5.stk j := by
      intro j hj
      simp [s6, SG.dSt, Function.update_apply, hj]
    have hs6V : s6.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
      rw [hs6o SG.sV (by decide)]; exact hs5V
    have hs6P : s6.stk SG.sP = Glyph.mk SG.sP :: bP := by
      rw [hs6o SG.sP (by decide)]; exact hs5P
    have hs6Q : s6.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      rw [hs6o SG.sQ (by decide)]; exact hs5Q
    have hs6R : s6.stk SG.sR = Glyph.mk SG.sR :: bR := by
      rw [hs6o SG.sR (by decide)]; exact hs5R
    have hs6U : s6.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
      rw [hs6o SG.sU (by decide)]; exact hs5U
    have hs6G : s6.stk SG.sG = s₀.stk SG.sG := by
      rw [hs6o SG.sG (by decide)]; exact hs5G
    -- 6b. copy `v` onto `sP`
    obtain ⟨s7, m7, hev7, hm7, hs7V, hs7P, hs7R, hs7S, hs7fr⟩ :=
      dup2EvalGen main SG.sV SG.sP SG.sR SG.sS SG.rgT vl bV bP bR bS s6
        hs6V hs6P hs6R hs6S (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hEv7 : Work.Layout.Ev main (SG.dup2 SG.sV SG.sP SG.sR SG.sS SG.rgT) s6 s7
        (100 + vl.length * 40) := ⟨m7, hev7, hm7⟩
    have hs7U : s7.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
      rw [hs7fr SG.sU (by decide) (by decide) (by decide) (by decide)]; exact hs6U
    have hs7Q : s7.stk SG.sQ = Glyph.mk SG.sQ :: bQ := by
      rw [hs7fr SG.sQ (by decide) (by decide) (by decide) (by decide)]; exact hs6Q
    have hs7G : s7.stk SG.sG = s₀.stk SG.sG := by
      rw [hs7fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs6G
    -- 6c. copy `u` onto `sQ`
    obtain ⟨s8, m8, hev8, hm8, hs8U, hs8Q, hs8R, hs8S, hs8fr⟩ :=
      dup2EvalGen main SG.sU SG.sQ SG.sR SG.sS SG.rgT ul bU bQ bR bS s7
        hs7U hs7Q hs7R hs7S (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hEv8 : Work.Layout.Ev main (SG.dup2 SG.sU SG.sQ SG.sR SG.sS SG.rgT) s7 s8
        (100 + ul.length * 40) := ⟨m8, hev8, hm8⟩
    have hs8P : s8.stk SG.sP = vl.map Glyph.bit ++ Glyph.mk SG.sP :: bP := by
      rw [hs8fr SG.sP (by decide) (by decide) (by decide) (by decide)]; exact hs7P
    have hs8V : s8.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
      rw [hs8fr SG.sV (by decide) (by decide) (by decide) (by decide)]; exact hs7V
    have hs8G : s8.stk SG.sG = s₀.stk SG.sG := by
      rw [hs8fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs7G
    -- 6d. ripple-subtract `sP - sQ` (= `v - u`) into `sS`
    obtain ⟨s9, m9, hev9, hm9, hs9P, hs9Q, hs9S, hs9C, hs9fr⟩ :=
      SGX.subLoopEvalXU main SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS
        SG.rgX SG.rgY SG.rgC SG.rgZ SG.rgT SG.rgU SG.rgW vl ul bP bQ s8
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (gcdBody2_mk_ne_eos SG.sP) (gcdBody2_mk_ne_eos SG.sQ)
        (fun c => gcdBody2_mk_ne_bit SG.sP c) (fun c => gcdBody2_mk_ne_bit SG.sQ c) hs8P hs8Q
    have hEv9 : Work.Layout.Ev main
        (SG.subLoop SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS
          SG.rgX SG.rgY SG.rgC SG.rgZ SG.rgT SG.rgU SG.rgW) s8 s9
        (40 * (max vl.length ul.length + 1) + 4) := ⟨m9, hev9, hm9⟩
    have hs9Sr : s9.stk SG.sS =
        ((SG.subDigits (max vl.length ul.length) vl ul false).2.reverse).map Glyph.bit
          ++ Glyph.mk SG.sS :: bS := by
      rw [hs9S, hs8S]
    have hs9V : s9.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
      rw [hs9fr SG.sV (by decide) (by decide) (by decide)]; exact hs8V
    have hs9U : s9.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
      rw [hs9fr SG.sU (by decide) (by decide) (by decide)]; exact hs8U
    have hs9R : s9.stk SG.sR = Glyph.mk SG.sR :: bR := by
      rw [hs9fr SG.sR (by decide) (by decide) (by decide)]; exact hs8R
    have hs9G : s9.stk SG.sG = s₀.stk SG.sG := by
      rw [hs9fr SG.sG (by decide) (by decide) (by decide)]; exact hs8G
    -- 6e. `v ← oddPart (v - u)`
    obtain ⟨s10, m10, hev10, hm10, hs10S, hs10P, hs10Q, hdisj10, hs10fr⟩ :=
      gcdTakeSpecMine main SG.sV ((SG.subDigits (max vl.length ul.length) vl ul false).2.reverse) vl
        bS bP bQ bV s9 (by decide) (by decide) (by decide) hs9Sr hs9P hs9Q hs9V
    -- the arithmetic of this second subtraction
    obtain ⟨hBr1, hBr2, hBr3, hBr4⟩ :=
      gcdBody2_subDigitsArith v u (max vl.length ul.length) vl ul (by rw [Nat.max_comm])
        hVval hUval
    have hbw2 : (SG.subDigits (max vl.length ul.length) vl ul false).1 = false := by
      cases h : (SG.subDigits (max vl.length ul.length) vl ul false).1 with
      | false => rfl
      | true => exact absurd (hBr1.mp h) (by omega)
    have hDlen2 : ((SG.subDigits (max vl.length ul.length) vl ul false).2.reverse).length
        = max vl.length ul.length := by rw [List.length_reverse, hBr4]
    obtain ⟨cT, hevT, hcT⟩ :=
      Work.Layout.Ev.seq hEv6a (Work.Layout.Ev.seq hEv7 (Work.Layout.Ev.seq hEv8
        (Work.Layout.Ev.seq hEv9 ⟨m10, hev10, le_rfl⟩)))
    have hev6 : Eval main (Cmd.ite SG.rgS1 (Glyph.bit true)
        (Work.Layout.seqs [SG.rLoop SG.sS (Glyph.mk SG.sS) none SG.rgT,
          SG.dup2 SG.sV SG.sP SG.sR SG.sS SG.rgT, SG.dup2 SG.sU SG.sQ SG.sR SG.sS SG.rgT,
          SG.subLoop SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS SG.rgX SG.rgY SG.rgC
            SG.rgZ SG.rgT SG.rgU SG.rgW,
          SG.gcdTake SG.sV])
        (SG.gcdTake SG.sU)) s5 s10 (cT + 1) := Eval.iteT hneS1 hevT
    have htot : Work.Layout.Ev main SG.gcdBody s s10 (5000 * (N + 1)) :=
      (Work.Layout.Ev.seq hEv1 (Work.Layout.Ev.seq hEv2 (Work.Layout.Ev.seq hEv3
        (Work.Layout.Ev.seq hEv4 (Work.Layout.Ev.seq hEv5 ⟨cT + 1, hev6, le_rfl⟩))))).mono (by
          have hm10b : m10 ≤ 40 * (max vl.length ul.length + vl.length + 1) + 40 := by
            have h := hm10; rw [hDlen2] at h; omega
          omega)
    obtain ⟨n10, hevbody, hnbody⟩ := htot
    have hs10U : s10.stk SG.sU = ul.map Glyph.bit ++ Glyph.mk SG.sU :: bU := by
      rw [hs10fr SG.sU (by decide) (by decide) (by decide) (by decide)]; exact hs9U
    have hs10R : s10.stk SG.sR = Glyph.mk SG.sR :: bR := by
      rw [hs10fr SG.sR (by decide) (by decide) (by decide) (by decide)]; exact hs9R
    have hs10G : s10.stk SG.sG = s₀.stk SG.sG := by
      rw [hs10fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs9G
    have hs10fr' : ∀ j : Stk, j ≠ SG.sU → j ≠ SG.sV → j ≠ SG.sG → j ≠ SG.sP → j ≠ SG.sQ →
        j ≠ SG.sR → j ≠ SG.sS → s10.stk j = s₀.stk j := by
      intro j h1 h2 h3 h4 h5 h6 h7
      have h9 : s9.stk j = s₀.stk j := by
        rw [hs9fr j h4 h5 h7, hs8fr j h1 h5 h6 h7, hs7fr j h2 h4 h6 h7, hs6o j h7]
        exact (hs5fr j h1 h2 h4 h5 h6 h7).trans (hs.hfr j h1 h2 h3 h4 h5 h6 h7)
      exact (hs10fr j h7 h4 h5 h2).trans h9
    have hbvalD : SG.bval ((SG.subDigits (max vl.length ul.length) vl ul false).2.reverse)
        = v - u := by
      rw [gcdBody2_bval_reverse]
      exact hBr2 hbw2
    have hbvalDne : SG.bval ((SG.subDigits (max vl.length ul.length) vl ul false).2.reverse) ≠ 0 := by
      rw [hbvalD]; omega
    rcases hdisj10 with ⟨h0, -, -⟩ | ⟨hne, ⟨l, hsl, hol, hllen⟩, hflag⟩
    · exact absurd h0 hbvalDne
    · have hnext : gNext u v = (u, SG.oddPart (v - u)) := by
        rw [gNext, if_neg (by omega : ¬ u = v), SG.gcdStep, if_neg (by omega : ¬ v ≤ u)]
      rw [hnext]
      refine ⟨s10, n10, hevbody, hnbody, ?_, ?_⟩
      · rw [hflag, if_neg (by omega : ¬ u = v)]
      · exact ⟨⟨ul, hs10U, hUval, hUlen⟩, ⟨l, hsl, (by rw [hol, hbvalD]),
            (by have h1 : l.length ≤ max vl.length ul.length := by rw [← hDlen2]; exact hllen
                omega)⟩, hs.hoddU, SG.oddPart_odd (v - u) (by omega),
            hs10P, hs10Q, hs10R, hs10S, hs10G, hs10fr'⟩
  · -- ### `v ≤ u`: `gcdTake sU`
    have hbwf : (SG.subDigits (max ul.length vl.length) ul vl false).1 = false := by
      cases h : (SG.subDigits (max ul.length vl.length) ul vl false).1 with
      | false => rfl
      | true => exact absurd h hbw
    have hle : v ≤ u := by
      have h1 : ¬ u < v := fun h => hbw (hAr1.mpr h)
      omega
    have hneS1 : s5.reg SG.rgS1 ≠ Glyph.bit true := by
      rw [hs5S1, hbwf]; exact gcdBody2_bit_false_ne_true
    obtain ⟨s10, m10, hev10, hm10, hs10S, hs10P, hs10Q, hdisj10, hs10fr⟩ :=
      gcdTakeSpecMine main SG.sU ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse) ul
        bS bP bQ bU s5 (by decide) (by decide) (by decide) hs5S hs5P hs5Q hs5U
    have hDlen : ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse).length
        = max ul.length vl.length := by rw [List.length_reverse, hAr4]
    have hbval10 : SG.bval ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse)
        = ofBits (SG.subDigits (max ul.length vl.length) ul vl false).2 :=
      gcdBody2_bval_reverse _
    have hev6 : Eval main (.ite SG.rgS1 (Glyph.bit true)
        (Work.Layout.seqs [SG.rLoop SG.sS (Glyph.mk SG.sS) none SG.rgT,
          SG.dup2 SG.sV SG.sP SG.sR SG.sS SG.rgT, SG.dup2 SG.sU SG.sQ SG.sR SG.sS SG.rgT,
          SG.subLoop SG.sP SG.sQ (Glyph.mk SG.sP) (Glyph.mk SG.sQ) SG.sS SG.rgX SG.rgY SG.rgC
            SG.rgZ SG.rgT SG.rgU SG.rgW,
          SG.gcdTake SG.sV])
        (SG.gcdTake SG.sU)) s5 s10 (m10 + 1) := Eval.iteF hneS1 hev10
    have htot : Work.Layout.Ev main SG.gcdBody s s10 (5000 * (N + 1)) :=
      (Work.Layout.Ev.seq hEv1 (Work.Layout.Ev.seq hEv2 (Work.Layout.Ev.seq hEv3
        (Work.Layout.Ev.seq hEv4 (Work.Layout.Ev.seq hEv5 ⟨m10 + 1, hev6, le_rfl⟩))))).mono (by
          have hm10b : m10 ≤ 40 * (max ul.length vl.length + ul.length + 1) + 40 := by
            have h := hm10; rw [hDlen] at h; omega
          omega)
    obtain ⟨n10, hevbody, hnbody⟩ := htot
    have hs10V : s10.stk SG.sV = vl.map Glyph.bit ++ Glyph.mk SG.sV :: bV := by
      rw [hs10fr SG.sV (by decide) (by decide) (by decide) (by decide)]; exact hs5V
    have hs10R : s10.stk SG.sR = Glyph.mk SG.sR :: bR := by
      rw [hs10fr SG.sR (by decide) (by decide) (by decide) (by decide)]; exact hs5R
    have hs10G : s10.stk SG.sG = s₀.stk SG.sG := by
      rw [hs10fr SG.sG (by decide) (by decide) (by decide) (by decide)]; exact hs5G
    have hs10fr' : ∀ j : Stk, j ≠ SG.sU → j ≠ SG.sV → j ≠ SG.sG → j ≠ SG.sP → j ≠ SG.sQ →
        j ≠ SG.sR → j ≠ SG.sS → s10.stk j = s₀.stk j := by
      intro j h1 h2 h3 h4 h5 h6 h7
      have h5' : s5.stk j = s.stk j := hs5fr j h1 h2 h4 h5 h6 h7
      exact (hs10fr j h7 h4 h5 h1).trans (h5'.trans (hs.hfr j h1 h2 h3 h4 h5 h6 h7))
    by_cases huv : u = v
    · -- ### `u = v`: the digits vanish, the loop stops
      rcases hdisj10 with ⟨h0, hsU10, hflag⟩ | ⟨hne, -, -⟩
      · have hnext : gNext u v = (u, v) := by rw [gNext, if_pos huv]
        rw [hnext]
        refine ⟨s10, n10, hevbody, hnbody, ?_, ?_⟩
        · rw [hflag, if_pos huv]
        · exact ⟨⟨ul, hsU10, hUval, hUlen⟩, ⟨vl, hs10V, hVval, hVlen⟩,
            hs.hoddU, hs.hoddV,
            hs10P, hs10Q, hs10R, hs10S, hs10G, hs10fr'⟩
      · exfalso
        exact hne (by rw [hbval10, hAr3.mpr huv])
    · -- ### `v < u`: `u ← oddPart (u - v)`
      have hlt : v < u := by omega
      rcases hdisj10 with ⟨h0, -, -⟩ | ⟨hne, ⟨l, hsl, hol, hllen⟩, hflag⟩
      · exfalso
        exact huv (hAr3.mp (by rw [← hbval10]; exact h0))
      · have hbval10' : SG.bval ((SG.subDigits (max ul.length vl.length) ul vl false).2.reverse)
            = u - v := by rw [hbval10]; exact hAr2 hbwf
        have hnext : gNext u v = (SG.oddPart (u - v), v) := by
          rw [gNext, if_neg huv, SG.gcdStep, if_pos hle]
        rw [hnext]
        refine ⟨s10, n10, hevbody, hnbody, ?_, ?_⟩
        · rw [hflag, if_neg huv]
        · exact ⟨⟨l, hsl, (by rw [hol, hbval10']),
            (by have h1' : l.length ≤ max ul.length vl.length := by rw [← hDlen]; exact hllen
                omega)⟩,
            ⟨vl, hs10V, hVval, hVlen⟩, SG.oddPart_odd (u - v) (by omega), hs.hoddV,
            hs10P, hs10Q, hs10R, hs10S, hs10G, hs10fr'⟩

end Work.IntLib.SqrtGcd

