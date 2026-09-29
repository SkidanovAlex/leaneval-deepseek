import Mathlib
import Submission.Work.IntLib.evCA.Defs

/-!
# `IntLib` / `evCarryAddAny`: the tail phase

`carryA` pushes the final carry of the ripple addition onto `aO` (if the counter `aCW` still has
units) or onto `a2` (if it is empty), and does nothing when the carry is clear; `popB_ev` drops the
`iend` terminator of the digit.  `evCATailEv` runs the tail `progTail = EvC.tailA` of the
`evCarryAddAny` word from the loop invariant `EvC.addP` at `EvC.addN W hbits` to `EvC.postP`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-- `carryA` with a clear carry does nothing. -/
theorem carryA_nocarry (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h : g Work.IntLib.EvC.rKa = HvdH.Glyph.bit false) :
    Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨g, X⟩ ⟨g, X⟩ 2 :=
  Work.Layout.Ev.iteF (by rw [Work.Layout.reg_mk, h]; decide) (Work.Layout.ev_skip main ⟨g, X⟩)

/-- `carryA` with a carry and a positive counter pushes the unit bit onto `aO`, consuming one
counter unit. -/
theorem carryA_low (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h : g Work.IntLib.EvC.rKa = HvdH.Glyph.bit true)
    (hc : (X Work.IntLib.aCW).headD HvdH.Glyph.eos = Work.IntLib.gTok) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph),
      Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨g, X⟩
        ⟨g', Function.update (Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
          Work.IntLib.aCW
          ((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).tail⟩ 6 := by
  have hpeek : Work.Layout.Ev main (.peek Work.IntLib.aCW Work.IntLib.EvC.rTa) ⟨g, X⟩
      ⟨Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok, X⟩ 1 := by
    have h1 := Work.Layout.ev_peek' main Work.IntLib.aCW Work.IntLib.EvC.rTa g X
    rw [hc] at h1
    exact h1
  have hset : Work.Layout.Ev main (.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true))
      ⟨Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok, X⟩
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
        Work.IntLib.EvC.rZa (HvdH.Glyph.bit true), X⟩ 1 :=
    Work.Layout.ev_set' main Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)
      (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok) X
  have hpush : Work.Layout.Ev main (.push Work.IntLib.aO Work.IntLib.EvC.rZa)
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
        Work.IntLib.EvC.rZa (HvdH.Glyph.bit true), X⟩
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
        Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
        Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO)⟩ 1 := by
    simpa only [Function.update_self] using
      Work.Layout.ev_push' main Work.IntLib.aO Work.IntLib.EvC.rZa
        (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
          Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) X
  have hpop : Work.Layout.Ev main (.pop Work.IntLib.aCW Work.IntLib.EvC.rTa)
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
        Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
        Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO)⟩
      ⟨Function.update (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
          Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) Work.IntLib.EvC.rTa
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).headD HvdH.Glyph.eos),
        Function.update (Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
          Work.IntLib.aCW
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).tail)⟩ 1 :=
    Work.Layout.ev_pop' main Work.IntLib.aCW Work.IntLib.EvC.rTa
      (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
        Work.IntLib.EvC.rZa (HvdH.Glyph.bit true))
      (Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
  have hinner : Work.Layout.Ev main
      (Work.Layout.seqs [.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
        .push Work.IntLib.aO Work.IntLib.EvC.rZa, .pop Work.IntLib.aCW Work.IntLib.EvC.rTa])
      ⟨Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok, X⟩
      ⟨Function.update (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
          Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) Work.IntLib.EvC.rTa
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).headD HvdH.Glyph.eos),
        Function.update (Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
          Work.IntLib.aCW
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).tail)⟩ 3 :=
    Work.Layout.Ev.seq' hset (Work.Layout.Ev.seq' hpush hpop (by omega : (1 : ℕ) + 1 ≤ 2))
      (by omega : (1 : ℕ) + 2 ≤ 3)
  have hite : Work.Layout.Ev main
      (.ite Work.IntLib.EvC.rTa Work.IntLib.gTok
        (Work.Layout.seqs [.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
          .push Work.IntLib.aO Work.IntLib.EvC.rZa, .pop Work.IntLib.aCW Work.IntLib.EvC.rTa])
        (.seq (.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) (.push Work.IntLib.a2 Work.IntLib.EvC.rZa)))
      ⟨Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok, X⟩
      ⟨Function.update (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
          Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) Work.IntLib.EvC.rTa
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).headD HvdH.Glyph.eos),
        Function.update (Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
          Work.IntLib.aCW
          (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
            Work.IntLib.aCW).tail)⟩ 4 :=
    Work.Layout.Ev.iteT (by rw [Work.Layout.reg_mk, Function.update_self]) hinner
  exact ⟨Function.update (Function.update (Function.update g Work.IntLib.EvC.rTa Work.IntLib.gTok)
      Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) Work.IntLib.EvC.rTa
      (((Function.update X Work.IntLib.aO (HvdH.Glyph.bit true :: X Work.IntLib.aO))
        Work.IntLib.aCW).headD HvdH.Glyph.eos),
    Work.Layout.Ev.iteT h (Work.Layout.Ev.seq' hpeek hite (by omega : (1 : ℕ) + 4 ≤ 5))⟩

/-- `carryA` with a carry and an exhausted counter pushes the unit bit onto `a2`. -/
theorem carryA_high (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h : g Work.IntLib.EvC.rKa = HvdH.Glyph.bit true)
    (hc : (X Work.IntLib.aCW).headD HvdH.Glyph.eos ≠ Work.IntLib.gTok) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph),
      Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨g, X⟩
        ⟨g', Function.update X Work.IntLib.a2 (HvdH.Glyph.bit true :: X Work.IntLib.a2)⟩ 5 := by
  have hpeek : Work.Layout.Ev main (.peek Work.IntLib.aCW Work.IntLib.EvC.rTa) ⟨g, X⟩
      ⟨Function.update g Work.IntLib.EvC.rTa ((X Work.IntLib.aCW).headD HvdH.Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main Work.IntLib.aCW Work.IntLib.EvC.rTa g X
  have hset : Work.Layout.Ev main (.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true))
      ⟨Function.update g Work.IntLib.EvC.rTa ((X Work.IntLib.aCW).headD HvdH.Glyph.eos), X⟩
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa
        ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true), X⟩ 1 :=
    Work.Layout.ev_set' main Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)
      (Function.update g Work.IntLib.EvC.rTa ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) X
  have hpush : Work.Layout.Ev main (.push Work.IntLib.a2 Work.IntLib.EvC.rZa)
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa
        ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true), X⟩
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa
        ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
        Function.update X Work.IntLib.a2 (HvdH.Glyph.bit true :: X Work.IntLib.a2)⟩ 1 := by
    simpa only [Function.update_self] using
      Work.Layout.ev_push' main Work.IntLib.a2 Work.IntLib.EvC.rZa
        (Function.update (Function.update g Work.IntLib.EvC.rTa
          ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) X
  have hite : Work.Layout.Ev main
      (.ite Work.IntLib.EvC.rTa Work.IntLib.gTok
        (Work.Layout.seqs [.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
          .push Work.IntLib.aO Work.IntLib.EvC.rZa, .pop Work.IntLib.aCW Work.IntLib.EvC.rTa])
        (.seq (.set Work.IntLib.EvC.rZa (HvdH.Glyph.bit true)) (.push Work.IntLib.a2 Work.IntLib.EvC.rZa)))
      ⟨Function.update g Work.IntLib.EvC.rTa ((X Work.IntLib.aCW).headD HvdH.Glyph.eos), X⟩
      ⟨Function.update (Function.update g Work.IntLib.EvC.rTa
          ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
        Function.update X Work.IntLib.a2 (HvdH.Glyph.bit true :: X Work.IntLib.a2)⟩ 3 :=
    Work.Layout.Ev.iteF hc (Work.Layout.Ev.seq' hset hpush (by omega : (1 : ℕ) + 1 ≤ 2))
  exact ⟨Function.update (Function.update g Work.IntLib.EvC.rTa
      ((X Work.IntLib.aCW).headD HvdH.Glyph.eos)) Work.IntLib.EvC.rZa (HvdH.Glyph.bit true),
    Work.Layout.Ev.iteT h (Work.Layout.Ev.seq' hpeek hite (by omega : (1 : ℕ) + 3 ≤ 4))⟩

/-- The `iend` terminator of the digit is dropped from `aB`. -/
theorem popB_ev (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (Bs : List HvdH.Glyph)
    (hB : X Work.IntLib.aB = HvdH.Glyph.iend :: Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph),
      Work.Layout.Ev main (.pop Work.IntLib.aB Work.IntLib.EvC.rGa) ⟨g, X⟩
        ⟨g', Function.update X Work.IntLib.aB (Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs)⟩ 1 := by
  have h1 : (X Work.IntLib.aB).headD HvdH.Glyph.eos = HvdH.Glyph.iend := by rw [hB]; rfl
  have h2 : (X Work.IntLib.aB).tail = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs := by rw [hB]; rfl
  refine ⟨Function.update g Work.IntLib.EvC.rGa HvdH.Glyph.iend, ?_⟩
  have hp := Work.Layout.ev_pop' main Work.IntLib.aB Work.IntLib.EvC.rGa g X
  rw [h1, h2] at hp
  exact hp

/-- The tail `EvC.tailA`: the final carry and the removal of the `iend`. -/
theorem evCATailEv (main : HvdH.Cmd) (b : ℕ) (W hbits LO : List Bool)
    (X : HvdH.Stk → List HvdH.Glyph) (Ws Os Cs A2s Bs : List HvdH.Glyph) (s : HvdH.State)
    (hP : Work.IntLib.EvC.addP b W hbits LO X Ws Os Cs A2s Bs (Work.IntLib.EvC.addN W hbits) s) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main Work.IntLib.EvCA.progTail s s' n ∧ n ≤ 9 ∧
      Work.IntLib.EvC.postP b W hbits LO Ws Os Cs A2s Bs s' ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aO → j ≠ Work.IntLib.a2 → j ≠ Work.IntLib.aCW →
        j ≠ Work.IntLib.aB → s'.stk j = s.stk j) := by
  obtain ⟨sg, sX⟩ := s
  obtain ⟨⟨hstrW, hstrB⟩, ⟨haccO, hacc2, haccCW⟩, _hfr, hKa, _hLa⟩ := hP
  simp only [Work.Layout.stk_mk] at hstrW hstrB haccO hacc2 haccCW
  simp only [Work.Layout.reg_mk] at hKa
  have hWn : W.drop (Work.IntLib.EvC.addN W hbits) = [] := List.drop_eq_nil_of_le (le_max_left _ _)
  have hBn : hbits.drop (Work.IntLib.EvC.addN W hbits) = [] :=
    List.drop_eq_nil_of_le (le_max_right _ _)
  have haW : sX aW = Shift.gmk aW :: Ws := by rw [hstrW, hWn]; rfl
  have haB : sX aB = Glyph.iend :: Shift.gmk aB :: Bs := by rw [hstrB, hBn]; rfl
  have hAlen : (Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits)).length =
      Work.IntLib.EvC.addN W hbits := Work.IntLib.EvC.accF_length W hbits false _
  have hcf : ∀ c : Bool, c = false ∨ c = true := by intro c; cases c <;> simp
  rcases hcf (Work.IntLib.EvC.carryC W hbits false (Work.IntLib.EvC.addN W hbits)) with hc | hc
  · -- the carry is clear: `carryA` is a skip
    have hcarry : Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨sg, sX⟩ ⟨sg, sX⟩ 2 :=
      carryA_nocarry main sg sX (by rw [hKa, hc])
    obtain ⟨g1, hpop⟩ := popB_ev main sg sX Bs haB
    have htail : Work.Layout.Ev main
        (Work.Layout.seqs [Work.IntLib.EvC.carryA, .pop Work.IntLib.aB Work.IntLib.EvC.rGa]) ⟨sg, sX⟩
        ⟨g1, Function.update sX aB (Shift.gmk aB :: Bs)⟩ 3 :=
      Work.Layout.Ev.seq' hcarry hpop (by omega : (2 : ℕ) + 1 ≤ 3)
    have hAddF : Work.IntLib.EvC.addAll W hbits =
        Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits) := by
      simp [Work.IntLib.EvC.addAll, hc]
    have hAllLen : (Work.IntLib.EvC.addAll W hbits).length = Work.IntLib.EvC.addN W hbits := by
      rw [hAddF, hAlen]
    refine ⟨_, 3, htail, by omega, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Function.update sX aB (Shift.gmk aB :: Bs)) aW = Shift.gmk aW :: Ws
      rw [Function.update_of_ne (by decide : aW ≠ aB)]; exact haW
    · show (Function.update sX aB (Shift.gmk aB :: Bs)) aB = Shift.gmk aB :: Bs
      rw [Function.update_self]
    · show (Function.update sX aB (Shift.gmk aB :: Bs)) aO =
        ((Work.IntLib.EvC.addAll W hbits).take b).reverse.map Glyph.bit ++
          LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os
      rw [Function.update_of_ne (by decide : aO ≠ aB), haccO, hAddF]
    · show (Function.update sX aB (Shift.gmk aB :: Bs)) a2 =
        ((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit ++ Shift.gmk a2 :: A2s
      rw [Function.update_of_ne (by decide : a2 ≠ aB), hacc2, hAddF]
    · show (Function.update sX aB (Shift.gmk aB :: Bs)) aCW =
        Work.IntLib.Unary (b - (Work.IntLib.EvC.addAll W hbits).length) (Shift.gmk aCW :: Cs)
      rw [Function.update_of_ne (by decide : aCW ≠ aB), haccCW, hAllLen]
    · intro j hjO hj2 hjC hjB
      show (Function.update sX aB (Shift.gmk aB :: Bs)) j = sX j
      rw [Function.update_of_ne hjB]
  · -- the carry is set
    have hAddT : Work.IntLib.EvC.addAll W hbits =
        Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits) ++ [true] := by
      simp [Work.IntLib.EvC.addAll, hc]
    have hAllLen : (Work.IntLib.EvC.addAll W hbits).length = Work.IntLib.EvC.addN W hbits + 1 := by
      rw [hAddT, List.length_append, hAlen]; simp
    rcases lt_or_ge (Work.IntLib.EvC.addN W hbits) b with hlt | hle
    · -- the counter still has a unit: the carry bit is finalised on `aO`
      have hpos : b - Work.IntLib.EvC.addN W hbits ≠ 0 := by omega
      have hhead : (sX aCW).headD Glyph.eos = Work.IntLib.gTok := by
        rw [haccCW]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
        rw [hm, Work.IntLib.Unary_succ]; rfl
      have htailCW : (sX aCW).tail =
          Work.IntLib.Unary (b - Work.IntLib.EvC.addN W hbits - 1) (Shift.gmk aCW :: Cs) := by
        rw [haccCW]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
        rw [hm, Work.IntLib.Unary_succ]; rfl
      obtain ⟨g1, hcarryRaw⟩ := carryA_low main sg sX (by rw [hKa, hc]) hhead
      set X1 : HvdH.Stk → List HvdH.Glyph :=
        Function.update (Function.update sX aO (Glyph.bit true :: sX aO)) aCW
          ((Function.update sX aO (Glyph.bit true :: sX aO)) aCW).tail with hX1
      have hcarry : Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨sg, sX⟩ ⟨g1, X1⟩ 6 := by
        rw [hX1]; exact hcarryRaw
      have hX1B : X1 aB = Glyph.iend :: Shift.gmk aB :: Bs := by
        rw [hX1, Function.update_of_ne (by decide : aB ≠ aCW),
          Function.update_of_ne (by decide : aB ≠ aO)]
        exact haB
      obtain ⟨g2, hpop⟩ := popB_ev main g1 X1 Bs hX1B
      have htail : Work.Layout.Ev main
          (Work.Layout.seqs [Work.IntLib.EvC.carryA, .pop Work.IntLib.aB Work.IntLib.EvC.rGa]) ⟨sg, sX⟩
          ⟨g2, Function.update X1 aB (Shift.gmk aB :: Bs)⟩ 7 :=
        Work.Layout.Ev.seq' hcarry hpop (by omega : (6 : ℕ) + 1 ≤ 7)
      have htake : (Work.IntLib.EvC.addAll W hbits).take b =
          Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits) ++ [true] := by
        rw [hAddT]
        apply List.take_of_length_le
        rw [List.length_append, hAlen]; simp; omega
      have hdropAll : (Work.IntLib.EvC.addAll W hbits).drop b = [] :=
        List.drop_eq_nil_of_le (by rw [hAllLen]; omega)
      have hdropA : (Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits)).drop b = [] :=
        List.drop_eq_nil_of_le (by rw [hAlen]; omega)
      have htakeA : (Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits)).take b =
          Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits) :=
        List.take_of_length_le (by rw [hAlen]; omega)
      refine ⟨_, 7, htail, by omega, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show (Function.update X1 aB (Shift.gmk aB :: Bs)) aW = Shift.gmk aW :: Ws
        rw [Function.update_of_ne (by decide : aW ≠ aB), hX1,
          Function.update_of_ne (by decide : aW ≠ aCW), Function.update_of_ne (by decide : aW ≠ aO)]
        exact haW
      · show (Function.update X1 aB (Shift.gmk aB :: Bs)) aB = Shift.gmk aB :: Bs
        rw [Function.update_self]
      · show (Function.update X1 aB (Shift.gmk aB :: Bs)) aO =
          ((Work.IntLib.EvC.addAll W hbits).take b).reverse.map Glyph.bit ++
            LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os
        rw [Function.update_of_ne (by decide : aO ≠ aB), hX1,
          Function.update_of_ne (by decide : aO ≠ aCW), Function.update_self, haccO, htake, htakeA]
        simp [List.reverse_append]
      · show (Function.update X1 aB (Shift.gmk aB :: Bs)) a2 =
          ((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit ++ Shift.gmk a2 :: A2s
        rw [Function.update_of_ne (by decide : a2 ≠ aB), hX1,
          Function.update_of_ne (by decide : a2 ≠ aCW), Function.update_of_ne (by decide : a2 ≠ aO),
          hacc2, hdropAll, hdropA]
        try rfl
      · show (Function.update X1 aB (Shift.gmk aB :: Bs)) aCW =
          Work.IntLib.Unary (b - (Work.IntLib.EvC.addAll W hbits).length) (Shift.gmk aCW :: Cs)
        rw [Function.update_of_ne (by decide : aCW ≠ aB), hX1, Function.update_self,
          Function.update_of_ne (by decide : aCW ≠ aO), htailCW, hAllLen]
        try congr 1
        try omega
      · intro j hjO hj2 hjC hjB
        show (Function.update X1 aB (Shift.gmk aB :: Bs)) j = sX j
        rw [Function.update_of_ne hjB, hX1, Function.update_of_ne hjC, Function.update_of_ne hjO]
    · -- the counter is exhausted: the carry bit goes to `a2`
      have hzero : b - Work.IntLib.EvC.addN W hbits = 0 := Nat.sub_eq_zero_of_le hle
      have hhead : (sX aCW).headD Glyph.eos ≠ Work.IntLib.gTok := by
        rw [haccCW, hzero, Work.IntLib.Unary_zero]
        exact Work.IntLib.gEnd_ne_gTok
      obtain ⟨g1, hcarryRaw⟩ := carryA_high main sg sX (by rw [hKa, hc]) hhead
      set X2 : HvdH.Stk → List HvdH.Glyph :=
        Function.update sX a2 (Glyph.bit true :: sX a2) with hX2
      have hcarry : Work.Layout.Ev main Work.IntLib.EvC.carryA ⟨sg, sX⟩ ⟨g1, X2⟩ 5 := by
        rw [hX2]; exact hcarryRaw
      have hX2B : X2 aB = Glyph.iend :: Shift.gmk aB :: Bs := by
        rw [hX2, Function.update_of_ne (by decide : aB ≠ a2)]
        exact haB
      obtain ⟨g2, hpop⟩ := popB_ev main g1 X2 Bs hX2B
      have htail : Work.Layout.Ev main
          (Work.Layout.seqs [Work.IntLib.EvC.carryA, .pop Work.IntLib.aB Work.IntLib.EvC.rGa]) ⟨sg, sX⟩
          ⟨g2, Function.update X2 aB (Shift.gmk aB :: Bs)⟩ 6 :=
        Work.Layout.Ev.seq' hcarry hpop (by omega : (5 : ℕ) + 1 ≤ 6)
      have htake : (Work.IntLib.EvC.addAll W hbits).take b =
          (Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits)).take b := by
        rw [hAddT]
        exact Work.IntLib.EvC.take_append_singleton_of_le _ _ (by rw [hAlen]; exact hle)
      have hdrop : (Work.IntLib.EvC.addAll W hbits).drop b =
          (Work.IntLib.EvC.accF W hbits false (Work.IntLib.EvC.addN W hbits)).drop b ++ [true] := by
        rw [hAddT]
        exact Work.IntLib.EvC.drop_append_singleton_of_le _ _ (by rw [hAlen]; exact hle)
      refine ⟨_, 6, htail, by omega, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show (Function.update X2 aB (Shift.gmk aB :: Bs)) aW = Shift.gmk aW :: Ws
        rw [Function.update_of_ne (by decide : aW ≠ aB), hX2, Function.update_of_ne (by decide : aW ≠ a2)]
        exact haW
      · show (Function.update X2 aB (Shift.gmk aB :: Bs)) aB = Shift.gmk aB :: Bs
        rw [Function.update_self]
      · show (Function.update X2 aB (Shift.gmk aB :: Bs)) aO =
          ((Work.IntLib.EvC.addAll W hbits).take b).reverse.map Glyph.bit ++
            LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os
        rw [Function.update_of_ne (by decide : aO ≠ aB), hX2, Function.update_of_ne (by decide : aO ≠ a2),
          haccO, htake]
      · show (Function.update X2 aB (Shift.gmk aB :: Bs)) a2 =
          ((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit ++ Shift.gmk a2 :: A2s
        rw [Function.update_of_ne (by decide : a2 ≠ aB), hX2, Function.update_self, hacc2, hdrop]
        simp [List.reverse_append]
      · show (Function.update X2 aB (Shift.gmk aB :: Bs)) aCW =
          Work.IntLib.Unary (b - (Work.IntLib.EvC.addAll W hbits).length) (Shift.gmk aCW :: Cs)
        rw [Function.update_of_ne (by decide : aCW ≠ aB), hX2, Function.update_of_ne (by decide : aCW ≠ a2),
          haccCW, hzero, hAllLen]
        congr 1
        omega
      · intro j hjO hj2 hjC hjB
        show (Function.update X2 aB (Shift.gmk aB :: Bs)) j = sX j
        rw [Function.update_of_ne hjB, hX2, Function.update_of_ne hj2]

end Work.IntLib
