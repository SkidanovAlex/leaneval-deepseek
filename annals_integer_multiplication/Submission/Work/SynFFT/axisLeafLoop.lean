import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.axisLeafDefs
import Submission.Work.SynFFT.leafFinal
import Submission.Work.SynFFT.leafElemStepEv
import Submission.Work.SynFFT.leafCloseStepEv
import Submission.Work.SynFFT.leafRowL
import Submission.Work.SynFFT.leafRowsL
import Submission.Work.Kernel.kernelLib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.copyIntTo_ev2
import Submission.Work.Layout.AA.clearAbove_ev
import Submission.Work.Layout.AA.decInt_ev2
import Submission.Work.Layout.reverseWord
import Submission.Work.IntLib.encodeNatBridge

set_option autoImplicit false

namespace Work.SynFFT

open HvdH
open Work.Layout
open Work.Layout.AA

/-! ## The leaf word of the blockwise transpose

This module collects the two long `Ev`-level lemmas of the leaf word of the blockwise
transpose (`lfLoop_run`, the main loop; `lfPrologue_ev`/`lfEpilogue_ev`, the marker
bookkeeping) and the assembly of the program `lfMain`, so that the file
`Submission/Work/SynFFT/axisLeaf.lean` only has to state the `WordR` contract. -/


/-! ## Small encodings facts -/

theorem ofList_cons_enc (x : HvdH.Val) (l : List HvdH.Val) :
    (HvdH.ofList (x :: l)).enc = HvdH.Glyph.cons :: (x.enc ++ (HvdH.ofList l).enc) := rfl

theorem ofList_nil_enc : (HvdH.ofList ([] : List HvdH.Val)).enc = [HvdH.Glyph.nil] := rfl

theorem ofList_singleton (x : HvdH.Val) : HvdH.ofList [x] = lfWrap x := rfl

theorem vsz_wrap (x : HvdH.Val) : HvdH.vsz (lfWrap x) = HvdH.vsz x + 2 := by
  simp [lfWrap, HvdH.vsz, HvdH.Val.enc]

theorem vsz_ofList_cons (w : HvdH.Val) (L : List HvdH.Val) :
    HvdH.vsz (HvdH.ofList (w :: L)) = HvdH.vsz w + HvdH.vsz (HvdH.ofList L) + 1 := by
  simp [HvdH.ofList, HvdH.vsz, HvdH.Val.enc, List.length_append]

/-! ## The loop -/

theorem lfLoop_run (main : HvdH.Cmd) (t B : ℕ) (W : List HvdH.Val) (hW : W.length = t * B)
    (hB : 1 ≤ B) :
    ∀ (l : List HvdH.Val), ∀ (P : List HvdH.Val), W = P ++ l →
      ∀ (rowL rowsL : List HvdH.Val) (c S : ℕ) (g : HvdH.Reg → HvdH.Glyph)
        (X Z : HvdH.Stk → List HvdH.Glyph),
        rowL = lfRowL B P → rowsL = lfRowsL t B W P → c = B - rowL.length →
        (rowL.map HvdH.vsz).sum ≤ S →
        X lfStF = (HvdH.ofList l).enc ++ gMark :: Z lfStF →
        X lfStBk = (HvdH.ofList rowL).enc ++ gMark :: Z lfStBk →
        X lfStBl = (HvdH.ofList rowsL).enc ++ gMark :: Z lfStBl →
        X lfStT4 = (HvdH.Val.int (c : ℤ)).enc ++ gMark :: Z lfStT4 →
        X lfStT2 = gMark :: Z lfStT2 →
        X lfStT5 = gMark :: Z lfStT5 →
        X lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl →
        (∀ k, k ≠ lfStF → k ≠ lfStBk → k ≠ lfStBl → k ≠ lfStT4 → k ≠ lfStT2 →
          k ≠ lfStT5 → k ≠ lfStEl → X k = Z k) →
        g lfF = HvdH.Glyph.cons →
        ∃ s', loopRuns main lfF HvdH.Glyph.cons lfBody (l.length + 1) ⟨g, X⟩ s'
            (lfTC B l c S + 2) ∧
          s'.reg lfF = HvdH.Glyph.eos ∧
          s'.stk lfStF = (HvdH.ofList []).enc ++ gMark :: Z lfStF ∧
          s'.stk lfStBk = (HvdH.ofList []).enc ++ gMark :: Z lfStBk ∧
          s'.stk lfStBl = (HvdH.ofList (lfRowsL t B W W)).enc ++ gMark :: Z lfStBl ∧
          s'.stk lfStT4 = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStT4 ∧
          s'.stk lfStT2 = gMark :: Z lfStT2 ∧
          s'.stk lfStT5 = gMark :: Z lfStT5 ∧
          s'.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl ∧
          (∀ k, k ≠ lfStF → k ≠ lfStBk → k ≠ lfStBl → k ≠ lfStT4 → k ≠ lfStT2 →
            k ≠ lfStT5 → k ≠ lfStEl → s'.stk k = Z k) := by
  intro l
  induction l with
  | nil =>
    intro P hP rowL rowsL c S g X Z hrow hrows hc hS hF hBk hBl hT4 hT2 hT5 hEl hoth hg
    have hPW : P = W := by rw [hP]; simp
    rw [hPW] at hrow hrows
    have hrowLen : rowL.length = 0 := by
      rw [hrow, leafRowL.1 B W, hW, Nat.mul_comm, Nat.mul_mod_right]
    have hrowNil : rowL = [] := List.eq_nil_of_length_eq_zero hrowLen
    have hcB : c = B := by rw [hc, hrowNil]; simp
    have hhead : (X lfStF).headD HvdH.Glyph.eos = HvdH.Glyph.nil := by rw [hF]; rfl
    have hpeek : Ev main (.peek lfStF lfP) ⟨g, X⟩
        ⟨Function.update g lfP HvdH.Glyph.nil, X⟩ 1 := by
      have h := ev_peek' main lfStF lfP g X
      rw [hhead] at h
      exact h
    have hset : Ev main (.set lfF HvdH.Glyph.eos)
        ⟨Function.update g lfP HvdH.Glyph.nil, X⟩
        ⟨Function.update (Function.update g lfP HvdH.Glyph.nil) lfF HvdH.Glyph.eos, X⟩ 1 :=
      ev_set' main lfF HvdH.Glyph.eos _ X
    have hbody : Ev main lfBody ⟨g, X⟩
        ⟨Function.update (Function.update g lfP HvdH.Glyph.nil) lfF HvdH.Glyph.eos, X⟩ 3 := by
      unfold lfBody
      simp only [seqs]
      exact Ev.seq hpeek (Ev.iteT (by simp) hset)
    have htc : lfTC B [] c S = 3 := rfl
    refine ⟨⟨Function.update (Function.update g lfP HvdH.Glyph.nil) lfF HvdH.Glyph.eos, X⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine loopRuns.mono (by omega) (loopRuns.one hg hbody) ?_
      rw [htc]; omega
    · simp
    · exact hF
    · simpa only [hrowNil] using hBk
    · simpa only [hrows] using hBl
    · simpa only [hcB] using hT4
    · exact hT2
    · exact hT5
    · exact hEl
    · intro k h1 h2 h3 h4 h5 h6 h7
      exact hoth k h1 h2 h3 h4 h5 h6 h7
  | cons x l' ih =>
    intro P hP rowL rowsL c S g X Z hrow hrows hc hS hF hBk hBl hT4 hT2 hT5 hEl hoth hg
    have hW2 : W = (P ++ [x]) ++ l' := by rw [hP]; simp
    have hrowLen : rowL.length = P.length % B := by rw [hrow]; exact leafRowL.1 B P
    have hmodB : P.length % B < B := Nat.mod_lt _ (by omega)
    have hc1 : 1 ≤ c := by rw [hc, hrowLen]; omega
    have hhead : (X lfStF).headD HvdH.Glyph.eos = HvdH.Glyph.cons := by rw [hF]; rfl
    have hpeek : Ev main (.peek lfStF lfP) ⟨g, X⟩
        ⟨Function.update g lfP HvdH.Glyph.cons, X⟩ 1 := by
      have h := ev_peek' main lfStF lfP g X
      rw [hhead] at h
      exact h
    -- one element step
    obtain ⟨s1, n1, h1ev, hn1, h1F, h1Bk, h1oth⟩ :=
      leafElemStepEv main (Function.update g lfP HvdH.Glyph.cons) X x
        ((HvdH.ofList l').enc ++ gMark :: Z lfStF) rowL (gMark :: Z lfStBk)
        (by rw [hF, ofList_cons_enc]; simp only [List.cons_append, List.append_assoc])
        (by rw [hBk])
    have hs1T4 : s1.stk lfStT4 = (HvdH.Val.int (c : ℤ)).enc ++ gMark :: Z lfStT4 := by
      rw [h1oth lfStT4 (by decide) (by decide)]; exact hT4
    have hs1T2 : s1.stk lfStT2 = gMark :: Z lfStT2 := by
      rw [h1oth lfStT2 (by decide) (by decide)]; exact hT2
    have hs1T5 : s1.stk lfStT5 = gMark :: Z lfStT5 := by
      rw [h1oth lfStT5 (by decide) (by decide)]; exact hT5
    have hs1Bl : s1.stk lfStBl = (HvdH.ofList rowsL).enc ++ gMark :: Z lfStBl := by
      rw [h1oth lfStBl (by decide) (by decide)]; exact hBl
    have hs1El : s1.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl := by
      rw [h1oth lfStEl (by decide) (by decide)]; exact hEl
    -- counter decrement
    obtain ⟨s2, n2, h2ev, hn2, h2T4, h2T2, h2oth⟩ :=
      decInt_ev2 main lfStT4 lfStT2 lfC1 lfF lfC3 lfC4 lfC5 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        s1.reg s1.stk (c - 1) (gMark :: Z lfStT4) (Z lfStT2)
        (by rw [hs1T4, Nat.sub_add_cancel hc1]) hs1T2
    have hn2' : n2 ≤ 40 * (HvdH.isz (c : ℤ) + 1) := by
      have h2 : (↑(c - 1) : ℤ) = (c : ℤ) - 1 := Nat.cast_sub hc1
      have h1 : (↑(c - 1) : ℤ) + 1 = (c : ℤ) := by rw [h2]; ring
      rw [h1] at hn2; exact hn2
    -- zero test
    obtain ⟨s3, n3, h3ev, hn3, h3T4, h3oth, h3rf⟩ :=
      isZeroInt_ev main lfStT4 lfC1 lfF lfC3 (by decide) (by decide) (by decide)
        s2.reg s2.stk (c - 1) (gMark :: Z lfStT4) (by rw [h2T4])
    have hs3T2 : s3.stk lfStT2 = gMark :: Z lfStT2 := by
      rw [h3oth lfStT2 (by decide), h2T2]
    have hs3T5 : s3.stk lfStT5 = gMark :: Z lfStT5 := by
      rw [h3oth lfStT5 (by decide), h2oth lfStT5 (by decide) (by decide), hs1T5]
    have hs3El : s3.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl := by
      rw [h3oth lfStEl (by decide), h2oth lfStEl (by decide) (by decide), hs1El]
    have hs3Bl : s3.stk lfStBl = (HvdH.ofList rowsL).enc ++ gMark :: Z lfStBl := by
      rw [h3oth lfStBl (by decide), h2oth lfStBl (by decide) (by decide), hs1Bl]
    have hs3Bk : s3.stk lfStBk = (HvdH.ofList (lfWrap x :: rowL)).enc ++ gMark :: Z lfStBk := by
      rw [h3oth lfStBk (by decide), h2oth lfStBk (by decide) (by decide), h1Bk, ofList_singleton]
    have hs3F : s3.stk lfStF = (HvdH.ofList l').enc ++ gMark :: Z lfStF := by
      rw [h3oth lfStF (by decide), h2oth lfStF (by decide) (by decide)]; exact h1F
    have hs3_oth : ∀ j, j ≠ lfStF → j ≠ lfStBk → j ≠ lfStBl → j ≠ lfStT4 → j ≠ lfStT2 →
        j ≠ lfStT5 → j ≠ lfStEl → s3.stk j = X j := by
      intro j h1 h2 h3 h4 h5 h6 h7
      rw [h3oth j h4, h2oth j h4 h5, h1oth j h1 h2, hoth j h1 h2 h3 h4 h5 h6 h7]
    by_cases hc1eq : c = 1
    · -- the row is complete
      have hcsub : c - 1 = 0 := by omega
      have hrf : s3.reg lfF = HvdH.Glyph.cons := h3rf.mp hcsub
      have hs3T4 : s3.stk lfStT4 = (HvdH.Val.int (0 : ℤ)).enc ++ gMark :: Z lfStT4 := by
        rw [h3T4, hcsub]; rfl
      -- counter bookkeeping
      have hmodEq : P.length % B = B - 1 := by
        have h : B - P.length % B = 1 := by rw [← hrowLen, ← hc]; exact hc1eq
        omega
      have hPlt : P.length < t * B := by
        have hlen : (P ++ [x] ++ l').length = t * B := by rw [← hW2, hW]
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      -- close step
      obtain ⟨s4, n4, h4ev, hn4, h4Bk, h4Bl, h4T4, h4reg, h4El, h4oth⟩ :=
        leafCloseStepEv main s3.reg s3.stk (lfWrap x :: rowL) rowsL B
          ((HvdH.Val.int (0 : ℤ)).enc) Z hs3Bk hs3Bl hs3T4 (gMark_not_mem_enc _) hs3El hs3T5
      -- the invariant for the next iteration
      have hrow' : ([] : List HvdH.Val) = lfRowL B (P ++ [x]) :=
        (leafRowL.2.2.1 B P x hB hmodEq).symm
      have hrows' : (HvdH.ofList (lfWrap x :: rowL) :: rowsL) = lfRowsL t B W (P ++ [x]) := by
        rw [leafRowsL.2.1 t B W P l' x hB hW2 hPlt hmodEq, hrows, hrow]
      have hc' : B = B - ([] : List HvdH.Val).length := by simp
      have hS' : (([] : List HvdH.Val).map HvdH.vsz).sum ≤ 0 := by simp
      -- state facts after the close
      have h4F : s4.stk lfStF = (HvdH.ofList l').enc ++ gMark :: Z lfStF := by
        rw [h4oth lfStF (by decide) (by decide) (by decide)]; exact hs3F
      have h4T2 : s4.stk lfStT2 = gMark :: Z lfStT2 := by
        rw [h4oth lfStT2 (by decide) (by decide) (by decide)]; exact hs3T2
      have h4T5 : s4.stk lfStT5 = gMark :: Z lfStT5 := by
        rw [h4oth lfStT5 (by decide) (by decide) (by decide)]; exact hs3T5
      have h4El' : s4.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl := by
        rw [h4El]; exact hs3El
      have h4_oth : ∀ k, k ≠ lfStF → k ≠ lfStBk → k ≠ lfStBl → k ≠ lfStT4 → k ≠ lfStT2 →
          k ≠ lfStT5 → k ≠ lfStEl → s4.stk k = Z k := by
        intro k h1 h2 h3 h4 h5 h6 h7
        rw [h4oth k h2 h3 h4, hs3_oth k h1 h2 h3 h4 h5 h6 h7, hoth k h1 h2 h3 h4 h5 h6 h7]
      have h4Bk' : s4.stk lfStBk = (HvdH.ofList ([] : List HvdH.Val)).enc ++ gMark :: Z lfStBk :=
        h4Bk
      have h4Bl' : s4.stk lfStBl =
          (HvdH.ofList (lfRowsL t B W (P ++ [x]))).enc ++ gMark :: Z lfStBl := by
        rw [hrows'] at h4Bl; exact h4Bl
      -- the rest of the loop
      obtain ⟨s5, hrun5, h5reg, h5F, h5Bk, h5Bl, h5T4, h5T2, h5T5, h5El, h5oth⟩ :=
        ih (P ++ [x]) hW2 [] (HvdH.ofList (lfWrap x :: rowL) :: rowsL) B 0 s4.reg s4.stk Z
          hrow' hrows' hc' hS' h4F h4Bk' h4Bl h4T4 h4T2 h4T5 h4El' h4_oth h4reg
      -- costs
      have hDglen : ((HvdH.Val.int (0 : ℤ)).enc).length = 2 := rfl
      have hiter : 1 + (n1 + (n2 + (n3 + (n4 + 1))) + 1) + 1 ≤ lfIter B x c S := by
        have hvsR : HvdH.vsz (HvdH.ofList (lfWrap x :: rowL)) + 1 ≤
            S + (HvdH.vsz x + 2) + B + 8 := by
          have h2 : rowL.length = B - 1 := by rw [hrowLen, hmodEq]
          have h3 := vsz_ofList_cons (lfWrap x) rowL
          have h4 := leafFinal.2.1 rowL
          have h5 := vsz_wrap x
          omega
        rw [lfIter, if_pos hc1eq]
        have hb1 : n1 ≤ 60 * (HvdH.vsz x + 1) := hn1
        have hb2 : n2 ≤ 40 * (HvdH.isz (c : ℤ) + 1) := hn2'
        have hb3 : n3 ≤ 10 := hn3
        have hb4 : n4 ≤ 20 * (HvdH.vsz (HvdH.ofList (lfWrap x :: rowL)) + 1) +
            16 * (HvdH.isz (B : ℤ) + 1) + 5 * ((HvdH.Val.int (0 : ℤ)).enc).length + 40 := hn4
        rw [hDglen] at hb4
        have hv := one_le_vsz x
        omega
      have hcost : (1 + (n1 + (n2 + (n3 + (n4 + 1))) + 1) + 1) + (lfTC B l' B 0 + 2) ≤
          lfTC B (x :: l') c S + 2 := by
        rw [show lfTC B (x :: l') c S = lfIter B x c S +
            lfTC B l' (if c = 1 then B else c - 1) (if c = 1 then 0 else S + (HvdH.vsz x + 2))
            from rfl]
        simp only [if_pos hc1eq]
        omega
      have hbody : Ev main lfBody ⟨g, X⟩ s4
          (1 + (n1 + (n2 + (n3 + (n4 + 1))) + 1)) := by
        unfold lfBody
        simp only [seqs]
        refine Ev.seq hpeek (Ev.iteF (by simp) ?_)
        refine Ev.seq h1ev (Ev.seq h2ev (Ev.seq h3ev ?_))
        exact Ev.iteT hrf h4ev
      refine ⟨s5, ?_, h5reg, h5F, h5Bk, h5Bl, h5T4, h5T2, h5T5, h5El, h5oth⟩
      refine loopRuns.cast (by simp only [List.length_cons]; omega)
        (loopRuns.mono (by omega) (loopRuns.concat (l'.length + 1)
        (loopRuns.one hg hbody) hrun5) hcost)
    · -- the row is not complete
      have hrf : s3.reg lfF ≠ HvdH.Glyph.cons := by
        intro hcon
        have h0 : c - 1 = 0 := h3rf.mpr hcon
        omega
      have hmodLt : P.length % B < B - 1 := by
        have h : B - P.length % B = c := by rw [← hrowLen, ← hc]
        omega
      have hsetF : Ev main (.set lfF HvdH.Glyph.cons) s3
          ⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ 1 :=
        ev_set' main lfF HvdH.Glyph.cons s3.reg s3.stk
      -- the invariant for the next iteration
      have hrow' : (lfWrap x :: rowL) = lfRowL B (P ++ [x]) := by
        rw [leafRowL.2.1 B P x hB hmodLt, hrow]
      have hrows' : rowsL = lfRowsL t B W (P ++ [x]) := by
        rw [leafRowsL.1 t B W P x hB hmodLt, hrows]
      have hc' : c - 1 = B - (lfWrap x :: rowL).length := by
        rw [List.length_cons, hc, hrowLen]; omega
      have hS' : ((lfWrap x :: rowL).map HvdH.vsz).sum ≤ S + (HvdH.vsz x + 2) := by
        rw [List.map_cons, List.sum_cons, vsz_wrap]
        omega
      have h4F : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStF =
          (HvdH.ofList l').enc ++ gMark :: Z lfStF := hs3F
      have h4Bk : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStBk =
          (HvdH.ofList (lfWrap x :: rowL)).enc ++ gMark :: Z lfStBk := hs3Bk
      have h4Bl : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStBl =
          (HvdH.ofList rowsL).enc ++ gMark :: Z lfStBl := hs3Bl
      have h4T4 : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStT4 =
          (HvdH.Val.int ((c - 1 : ℕ) : ℤ)).enc ++ gMark :: Z lfStT4 := h3T4
      have h4T2 : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStT2 =
          gMark :: Z lfStT2 := hs3T2
      have h4T5 : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStT5 =
          gMark :: Z lfStT5 := hs3T5
      have h4El : (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk lfStEl =
          (HvdH.Val.int (B : ℤ)).enc ++ gMark :: Z lfStEl := hs3El
      have h4_oth : ∀ k, k ≠ lfStF → k ≠ lfStBk → k ≠ lfStBl → k ≠ lfStT4 → k ≠ lfStT2 →
          k ≠ lfStT5 → k ≠ lfStEl →
          (⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩ : HvdH.State).stk k = Z k := by
        intro k h1 h2 h3 h4 h5 h6 h7
        exact (hs3_oth k h1 h2 h3 h4 h5 h6 h7).trans (hoth k h1 h2 h3 h4 h5 h6 h7)
      obtain ⟨s5, hrun5, h5reg, h5F, h5Bk, h5Bl, h5T4, h5T2, h5T5, h5El, h5oth⟩ :=
        ih (P ++ [x]) hW2 (lfWrap x :: rowL) rowsL (c - 1) (S + (HvdH.vsz x + 2))
          (Function.update s3.reg lfF HvdH.Glyph.cons) s3.stk Z
          hrow' hrows' hc' hS' h4F h4Bk h4Bl h4T4 h4T2 h4T5 h4El h4_oth (by simp)
      -- costs
      have hiter : 1 + (n1 + (n2 + (n3 + (1 + 1))) + 1) + 1 ≤ lfIter B x c S := by
        rw [lfIter, if_neg hc1eq]
        have hb1 : n1 ≤ 60 * (HvdH.vsz x + 1) := hn1
        have hb2 : n2 ≤ 40 * (HvdH.isz (c : ℤ) + 1) := hn2'
        have hb3 : n3 ≤ 10 := hn3
        have hv := one_le_vsz x
        omega
      have hcost : (1 + (n1 + (n2 + (n3 + (1 + 1))) + 1) + 1) +
            (lfTC B l' (c - 1) (S + (HvdH.vsz x + 2)) + 2) ≤
          lfTC B (x :: l') c S + 2 := by
        rw [show lfTC B (x :: l') c S = lfIter B x c S +
            lfTC B l' (if c = 1 then B else c - 1) (if c = 1 then 0 else S + (HvdH.vsz x + 2))
            from rfl]
        simp only [if_neg hc1eq]
        omega
      have hbody : Ev main lfBody ⟨g, X⟩
          ⟨Function.update s3.reg lfF HvdH.Glyph.cons, s3.stk⟩
          (1 + (n1 + (n2 + (n3 + (1 + 1))) + 1)) := by
        unfold lfBody
        simp only [seqs]
        refine Ev.seq hpeek (Ev.iteF (by simp) ?_)
        refine Ev.seq h1ev (Ev.seq h2ev (Ev.seq h3ev ?_))
        exact Ev.iteF hrf hsetF
      refine ⟨s5, ?_, h5reg, h5F, h5Bk, h5Bl, h5T4, h5T2, h5T5, h5El, h5oth⟩
      refine loopRuns.cast (by simp only [List.length_cons]; omega)
        (loopRuns.mono (by omega) (loopRuns.concat (l'.length + 1)
        (loopRuns.one hg hbody) hrun5) hcost)

/-! ## Prologue and epilogue -/

theorem lfPrologue_ev (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) :
    ∃ s' n, Ev main lfPrologue ⟨g, X⟩ s' n ∧ n ≤ 3 * lfStks.length + 1 ∧
      (∀ k, k ∈ lfStks → s'.stk k = gMark :: X k) ∧
      (∀ k, k ∉ lfStks → s'.stk k = X k) := by
  have hnod : lfStks.Nodup := by decide
  suffices h : ∀ (ks : List HvdH.Stk), ks.Nodup → ∀ (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      ∃ s' n, Ev main (seqs (ks.map (fun k => lfPushMarkS k lfQ))) ⟨g, X⟩ s' n ∧
        n ≤ 3 * ks.length + 1 ∧
        (∀ k, k ∈ ks → s'.stk k = gMark :: X k) ∧
        (∀ k, k ∉ ks → s'.stk k = X k) by
    obtain ⟨s', n, he, hn, h1, h2⟩ := h lfStks hnod g X
    exact ⟨s', n, he, hn, h1, h2⟩
  intro ks
  induction ks with
  | nil =>
    intro _ g X
    refine ⟨⟨g, X⟩, 1, ?_, by simp, ?_, ?_⟩
    · simpa using Ev.seqs_nil (main := main) (s := (⟨g, X⟩ : HvdH.State))
    · intro k hk; simp at hk
    · intro k _; rfl
  | cons a t ih =>
    intro hnd g X
    obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
    obtain ⟨s1, n1, h1, hn1, ha1, ht1⟩ := pushGlyphs_ev main [gMark] a lfQ g X
    obtain ⟨s2, n2, h2, hn2, ha2, ht2⟩ := ih hndt s1.reg s1.stk
    refine ⟨s2, n1 + n2, Ev.seqs_cons h1 h2, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hn1 ⊢
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with h | h
      · rw [h, ht2 a hna, ha1]; rfl
      · rw [ha2 k h, ht1 k (fun hh => hna (hh ▸ h))]
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
      have hkt : k ∉ t := fun h => hk (List.mem_cons_of_mem a h)
      rw [ht2 k hkt, ht1 k hka]

theorem lfEpilogue_ev (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (D Z : HvdH.Stk → List HvdH.Glyph)
    (hD : ∀ k, k ∈ lfStks → gMark ∉ D k) (hX : ∀ k, k ∈ lfStks → X k = D k ++ gMark :: Z k) :
    ∃ s' n, Ev main lfEpilogue ⟨g, X⟩ s' n ∧
      n ≤ 5 * (lfStks.map (fun k => (D k).length)).sum + 9 * lfStks.length + 1 ∧
      (∀ k, k ∈ lfStks → s'.stk k = Z k) ∧
      (∀ k, k ∉ lfStks → s'.stk k = X k) := by
  have hnod : lfStks.Nodup := by decide
  suffices h : ∀ (ks : List HvdH.Stk), ks.Nodup →
      ∀ (D Z : HvdH.Stk → List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      (∀ k, k ∈ ks → gMark ∉ D k) → (∀ k, k ∈ ks → X k = D k ++ gMark :: Z k) →
      ∃ s' n, Ev main (seqs (ks.map (fun k => clearTo k lfP lfF))) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (ks.map (fun k => (D k).length)).sum + 9 * ks.length + 1 ∧
        (∀ k, k ∈ ks → s'.stk k = Z k) ∧ (∀ k, k ∉ ks → s'.stk k = X k) by
    obtain ⟨s', n, he, hn, h1, h2⟩ := h lfStks hnod D Z g X hD hX
    exact ⟨s', n, he, hn, h1, h2⟩
  intro ks
  induction ks with
  | nil =>
    intro _ D Z g X _ _
    refine ⟨⟨g, X⟩, 1, ?_, by simp, ?_, ?_⟩
    · simpa using Ev.seqs_nil (main := main) (s := (⟨g, X⟩ : HvdH.State))
    · intro k hk; simp at hk
    · intro k _; rfl
  | cons a t ih =>
    intro hnd D Z g X hD hX
    obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
    obtain ⟨s1, n1, h1, hn1, ha1, hta1⟩ :=
      clearTo_ev main a lfP lfF (by decide) g X (D a) (Z a) (hD a (by simp)) (hX a (by simp))
    obtain ⟨s2, n2, h2, hn2, ha2, ht2⟩ :=
      ih hndt D Z s1.reg s1.stk
        (fun k hk => hD k (List.mem_cons_of_mem a hk))
        (fun k hk => (hta1 k (fun h => hna (h ▸ hk))).trans (hX k (List.mem_cons_of_mem a hk)))
    refine ⟨s2, n1 + n2, Ev.seqs_cons h1 h2, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.map_cons, List.sum_cons] at hn2 ⊢
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with h | h
      · rw [h, ht2 a hna, ha1]
      · exact ha2 k h
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
      have hkt : k ∉ t := fun h => hk (List.mem_cons_of_mem a h)
      rw [ht2 k hkt, hta1 k hka]

/-! ## The assembled program -/

def lfSetup : Cmd :=
  seqs [mvVal 0 lfStF lfCA lfCB, mvVal 0 lfCA lfCB lfStM1,
        copyIntTo 0 lfStEl lfStT5 lfC1 lfF, copyIntTo lfStEl lfStT4 lfStT5 lfC1 lfF,
        mvVal lfCA 0 lfCB lfStM1, pushNil lfStBk lfQ, pushNil lfStBl lfQ]

def lfFinish : Cmd := seqs [mvVal lfStBl 0 lfCA lfCB, lfEpilogue]

def lfMain (revP : Cmd) : Cmd := seqs [lfPrologue, revP, lfSetup, lfLoop, lfFinish]

theorem vsz_int (z : ℤ) : HvdH.vsz (HvdH.Val.int z) = HvdH.isz z := by
  simp [HvdH.vsz, HvdH.isz, HvdH.Val.enc, Work.IntLib.encodeNat_length]

theorem nat_size_le_self (n : ℕ) : n.size ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Nat.size_le.mpr Nat.lt_two_pow_self

end Work.SynFFT
