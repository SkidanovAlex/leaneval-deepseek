import Mathlib
import Submission.Work.SynFFT.axisLeafDefs
import Submission.Work.SynFFT.prependToScratchEv
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.copyIntTo_ev2
import Submission.Work.Layout.AA.clearAbove_ev
import Submission.Work.Layout.AA.prependTo_ev

namespace Work.SynFFT

open HvdH

theorem leafCloseStepEv (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph) (R L : List HvdH.Val) (B : ℕ)
    (Dg : List HvdH.Glyph) (Z : HvdH.Stk → List HvdH.Glyph)
    (hR : X Work.SynFFT.lfStBk = (HvdH.ofList R).enc ++ Work.Layout.gMark :: Z Work.SynFFT.lfStBk)
    (hL : X Work.SynFFT.lfStBl = (HvdH.ofList L).enc ++ Work.Layout.gMark :: Z Work.SynFFT.lfStBl)
    (hDg : X Work.SynFFT.lfStT4 = Dg ++ Work.Layout.gMark :: Z Work.SynFFT.lfStT4)
    (hDgf : Work.Layout.gMark ∉ Dg)
    (hEl : X Work.SynFFT.lfStEl =
      (HvdH.Val.int (B : ℤ)).enc ++ Work.Layout.gMark :: Z Work.SynFFT.lfStEl)
    (hT5 : X Work.SynFFT.lfStT5 = Work.Layout.gMark :: Z Work.SynFFT.lfStT5) :
    ∃ s' n, Work.Layout.Ev main Work.SynFFT.lfCloseStep ⟨g, X⟩ s' n ∧
      n ≤ 20 * (HvdH.vsz (HvdH.ofList R) + 1) + 16 * (HvdH.isz (B : ℤ) + 1) +
        5 * Dg.length + 40 ∧
      s'.stk Work.SynFFT.lfStBk =
        HvdH.Glyph.nil :: (Work.Layout.gMark :: Z Work.SynFFT.lfStBk) ∧
      s'.stk Work.SynFFT.lfStBl =
        (HvdH.ofList (HvdH.ofList R :: L)).enc ++ Work.Layout.gMark :: Z Work.SynFFT.lfStBl ∧
      s'.stk Work.SynFFT.lfStT4 =
        (HvdH.Val.int (B : ℤ)).enc ++ Work.Layout.gMark :: Z Work.SynFFT.lfStT4 ∧
      s'.reg Work.SynFFT.lfF = HvdH.Glyph.cons ∧
      s'.stk Work.SynFFT.lfStEl = X Work.SynFFT.lfStEl ∧
      (∀ j, j ≠ Work.SynFFT.lfStBk → j ≠ Work.SynFFT.lfStBl → j ≠ Work.SynFFT.lfStT4 →
        s'.stk j = X j) := by
  -- step 1: move the row value `ofList R` from `lfStBk` onto the front of the row list `lfStBl`
  obtain ⟨s1, n1, h1, hn1, ha1, hb1, _, _, hf1⟩ :=
    prependToScratchEv main lfStBk lfStBl lfCA lfCB lfP (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) g X (HvdH.ofList R) L
      (Work.Layout.gMark :: Z lfStBk) (Work.Layout.gMark :: Z lfStBl) hR hL
  -- step 2: push a fresh empty row on `lfStBk`
  obtain ⟨s2, n2, h2, hn2, hbk2, hf2⟩ :=
    Work.Layout.AA.pushNil_ev main lfStBk lfQ s1.reg s1.stk
  have h2' : Work.Layout.Ev main (lfPushNilS lfStBk lfQ) s1 s2 5 := h2.mono (by omega)
  -- step 3: clear the old counter on `lfStT4` down to its marker
  have hs2T4 : s2.stk lfStT4 = Dg ++ Work.Layout.gMark :: Z lfStT4 := by
    rw [hf2 lfStT4 (by decide), hf1 lfStT4 (by decide) (by decide)]
    exact hDg
  obtain ⟨s3, n3, h3, hn3, hT4_3, hf3⟩ :=
    Work.Layout.AA.clearAbove_ev main lfStT4 lfP lfF (by decide) s2.reg s2.stk Dg (Z lfStT4)
      hDgf hs2T4
  -- step 4: copy the counter template `int B` from `lfStEl` onto `lfStT4`
  have hs3El : s3.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ Work.Layout.gMark :: Z lfStEl := by
    rw [hf3 lfStEl (by decide), hf2 lfStEl (by decide), hf1 lfStEl (by decide) (by decide)]
    exact hEl
  have hs3T5 : s3.stk lfStT5 = Work.Layout.gMark :: Z lfStT5 := by
    rw [hf3 lfStT5 (by decide), hf2 lfStT5 (by decide), hf1 lfStT5 (by decide) (by decide)]
    exact hT5
  obtain ⟨s4, n4, h4, hn4, hEl4, hT4_4, hT5_4, hf4⟩ :=
    Work.Layout.AA.copyIntTo_ev2 main lfStEl lfStT4 lfStT5 lfC1 lfF (by decide) (by decide)
      (by decide) (by decide) s3.reg s3.stk B (Work.Layout.gMark :: Z lfStEl)
      (Work.Layout.gMark :: Z lfStT4) (Z lfStT5) hs3El hT4_3 hs3T5
  -- step 5: set the "continue" flag
  have h5 : Work.Layout.Ev main (HvdH.Cmd.set lfF HvdH.Glyph.cons) s4
      ⟨Function.update s4.reg lfF HvdH.Glyph.cons, s4.stk⟩ 1 :=
    Work.Layout.ev_set main lfF HvdH.Glyph.cons s4
  -- assemble the five steps
  have e1 : Work.Layout.Ev main (Work.Layout.prependTo lfStBk lfStBl lfCA lfCB lfP) ⟨g, X⟩ s1
      (20 * (HvdH.vsz (HvdH.ofList R) + 1) + 4) := h1.mono hn1
  have e2 : Work.Layout.Ev main (lfPushNilS lfStBk lfQ) s1 s2 5 := h2.mono hn2
  have e3 : Work.Layout.Ev main (Work.Layout.clearAbove lfStT4 lfP lfF) s2 s3
      (5 * Dg.length + 10) := h3.mono hn3
  have e4 : Work.Layout.Ev main (Work.Layout.copyIntTo lfStEl lfStT4 lfStT5 lfC1 lfF) s3 s4
      (16 * (HvdH.isz (B : ℤ) + 1)) := h4.mono hn4
  have e12345 : Work.Layout.Ev main
      (Work.Layout.seqs [Work.Layout.prependTo lfStBk lfStBl lfCA lfCB lfP, lfPushNilS lfStBk lfQ,
        Work.Layout.clearAbove lfStT4 lfP lfF,
        Work.Layout.copyIntTo lfStEl lfStT4 lfStT5 lfC1 lfF,
        HvdH.Cmd.set lfF HvdH.Glyph.cons]) ⟨g, X⟩
      ⟨Function.update s4.reg lfF HvdH.Glyph.cons, s4.stk⟩
      (20 * (HvdH.vsz (HvdH.ofList R) + 1) + 4 + (5 + (5 * Dg.length + 10 +
        (16 * (HvdH.isz (B : ℤ) + 1) + (1 + 1))))) :=
    Work.Layout.Ev.seqs_cons e1 (Work.Layout.Ev.seqs_cons e2
      (Work.Layout.Ev.seqs_cons e3 (Work.Layout.Ev.seqs_cons e4
        (Work.Layout.Ev.seqs_cons h5 Work.Layout.Ev.seqs_nil))))
  have hmain : Work.Layout.Ev main lfCloseStep ⟨g, X⟩
      ⟨Function.update s4.reg lfF HvdH.Glyph.cons, s4.stk⟩
      (20 * (HvdH.vsz (HvdH.ofList R) + 1) + 16 * (HvdH.isz (B : ℤ) + 1) +
        5 * Dg.length + 40) := by
    unfold lfCloseStep
    exact e12345.mono (by omega)
  refine ⟨⟨Function.update s4.reg lfF HvdH.Glyph.cons, s4.stk⟩,
    20 * (HvdH.vsz (HvdH.ofList R) + 1) + 16 * (HvdH.isz (B : ℤ) + 1) + 5 * Dg.length + 40,
    hmain, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- new empty row on `lfStBk`
    show s4.stk lfStBk = HvdH.Glyph.nil :: (Work.Layout.gMark :: Z lfStBk)
    rw [hf4 lfStBk (by decide) (by decide) (by decide), hf3 lfStBk (by decide),
      hbk2, ha1]
    rfl
  · -- the completed row prepended to the row list on `lfStBl`
    show s4.stk lfStBl =
      (HvdH.ofList (HvdH.ofList R :: L)).enc ++ Work.Layout.gMark :: Z lfStBl
    rw [hf4 lfStBl (by decide) (by decide) (by decide), hf3 lfStBl (by decide),
      hf2 lfStBl (by decide), hb1]
  · -- the fresh counter on `lfStT4`
    show s4.stk lfStT4 = (HvdH.Val.int (B : ℤ)).enc ++ Work.Layout.gMark :: Z lfStT4
    exact hT4_4
  · -- the flag register
    show (Function.update s4.reg lfF HvdH.Glyph.cons) lfF = HvdH.Glyph.cons
    simp
  · -- the counter template on `lfStEl` is unchanged
    show s4.stk lfStEl = X lfStEl
    exact hEl4.trans hEl.symm
  · -- frame for every other stack
    intro j hj2 hj3 hj4
    show s4.stk j = X j
    rcases eq_or_ne j lfStT5 with hj6 | hj6
    · subst hj6
      exact hT5_4.trans hT5.symm
    · rcases eq_or_ne j lfStEl with hj7 | hj7
      · subst hj7
        exact hEl4.trans hEl.symm
      · rw [hf4 j hj7 hj4 hj6, hf3 j hj4, hf2 j hj2, hf1 j hj2 hj3]

end Work.SynFFT
