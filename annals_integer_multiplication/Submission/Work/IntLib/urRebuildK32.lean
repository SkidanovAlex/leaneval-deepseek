import Mathlib
import Submission.Work.IntLib.unaryRebuild
import Submission.Work.IntLib.evalMachine

namespace Work.IntLib

open HvdH
open Work.Layout

/-- The `unaryRebuild` gadget with its witnesses made explicit: the program is `UR.urProg a tgt c tr`
and the constant of the cost bound is `32` (the existential form `Work.IntLib.unaryRebuild` is
opaque, so its witnesses cannot be recovered definitionally). -/
theorem urRebuildK32 (main : HvdH.Cmd) (a tgt c tr : HvdH.Stk)
    (hat : a ≠ tgt) (hac : a ≠ c) (hac' : a ≠ tr) (htc : tgt ≠ c) (htt : tgt ≠ tr) (hct : c ≠ tr)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (bs : List Bool)
    (Gs Gt Gc Gs' : List HvdH.Glyph)
    (ha : X a = (HvdH.Glyph.iend :: (bs.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos])) ++ HvdH.Glyph.mk a :: Gs)
    (htgt : X tgt = Gt) (hc : X c = Gc) (htr : X tr = Gs') :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main (Work.IntLib.UR.urProg a tgt c tr) ⟨g, X⟩ s' n ∧
      n ≤ 32 * (bs.length + Work.IntLib.ofBits bs + 1) ∧
      s'.stk a = HvdH.Glyph.mk a :: Gs ∧
      s'.stk tgt = (HvdH.Glyph.pos :: (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend])) ++ Gt ∧
      s'.stk c = Work.IntLib.Unary (Work.IntLib.ofBits bs) Gc ∧
      s'.stk tr = Gs' ∧
      (∀ k : HvdH.Stk, k ≠ a → k ≠ tgt → k ≠ c → k ≠ tr → s'.stk k = X k) := by
  have hat' : tgt ≠ a := fun h => hat h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hctg : c ≠ tgt := fun h => htc h.symm
  have htra : tr ≠ a := fun h => hac' h.symm
  have httgt : tr ≠ tgt := fun h => htt h.symm
  have htrc : tr ≠ c := fun h => hct h.symm
  set g1 : Reg → Glyph := Function.update g UR.rIend Glyph.iend with hg1
  set X2 : Stk → List Glyph := Function.update X tgt (Glyph.iend :: X tgt) with hX2
  set g3 : Reg → Glyph := Function.update g1 UR.rTok gTok with hg3
  set g4 : Reg → Glyph := Function.update g3 UR.rPos Glyph.pos with hg4
  set g5 : Reg → Glyph := Function.update g4 UR.rScr gEnd with hg5
  set X6 : Stk → List Glyph := Function.update X2 c (gEnd :: X2 c) with hX6
  set g7 : Reg → Glyph := Function.update g5 UR.rScr ((X6 a).headD .eos) with hg7
  set X7 : Stk → List Glyph := Function.update X6 a (X6 a).tail with hX7
  set g8 : Reg → Glyph := Function.update g7 UR.rT gTok with hg8
  have e1 : Ev main (.set UR.rIend Glyph.iend) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    rw [hg1]; exact ev_set' main UR.rIend Glyph.iend g X
  have hg1rIend : g1 UR.rIend = Glyph.iend := by
    rw [hg1]; exact Function.update_self UR.rIend Glyph.iend g
  have e2 : Ev main (.push tgt UR.rIend) ⟨g1, X⟩ ⟨g1, X2⟩ 1 := by
    have h := ev_push' main tgt UR.rIend g1 X
    rw [hg1rIend] at h
    rw [hX2]
    exact h
  have e3 : Ev main (.set UR.rTok gTok) ⟨g1, X2⟩ ⟨g3, X2⟩ 1 := by
    rw [hg3]; exact ev_set' main UR.rTok gTok g1 X2
  have e4 : Ev main (.set UR.rPos Glyph.pos) ⟨g3, X2⟩ ⟨g4, X2⟩ 1 := by
    rw [hg4]; exact ev_set' main UR.rPos Glyph.pos g3 X2
  have e5 : Ev main (.set UR.rScr gEnd) ⟨g4, X2⟩ ⟨g5, X2⟩ 1 := by
    rw [hg5]; exact ev_set' main UR.rScr gEnd g4 X2
  have hg5rScr : g5 UR.rScr = gEnd := by
    rw [hg5]; exact Function.update_self UR.rScr gEnd g4
  have e6 : Ev main (.push c UR.rScr) ⟨g5, X2⟩ ⟨g5, X6⟩ 1 := by
    have h := ev_push' main c UR.rScr g5 X2
    rw [hg5rScr] at h
    rw [hX6]
    exact h
  have e7 : Ev main (.pop a UR.rScr) ⟨g5, X6⟩ ⟨g7, X7⟩ 1 := by
    rw [hg7, hX7]; exact ev_pop' main a UR.rScr g5 X6
  have e8 : Ev main (.set UR.rT gTok) ⟨g7, X7⟩ ⟨g8, X7⟩ 1 := by
    rw [hg8]; exact ev_set' main UR.rT gTok g7 X7
  have ha0 : (Glyph.iend :: (bs.reverse.map Glyph.bit ++ [Glyph.pos])) ++ Glyph.mk a :: Gs
      = Glyph.iend :: (bs.reverse.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs) := by
    simp [List.cons_append, List.append_assoc]
  have hX6a : X6 a = X a := by
    rw [hX6, Function.update_of_ne hac (gEnd :: X2 c) X2, hX2,
      Function.update_of_ne hat (Glyph.iend :: X tgt) X]
  have hX7a : X7 a = bs.reverse.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs := by
    rw [hX7, Function.update_self a (X6 a).tail X6, hX6a, ha, ha0, List.tail_cons]
  have hX6c : X6 c = Unary 0 Gc := by
    rw [hX6, Function.update_self c (gEnd :: X2 c) X2, hX2,
      Function.update_of_ne hctg (Glyph.iend :: X tgt) X, hc, Unary_zero]
  have hX7c : X7 c = Unary 0 Gc :=
    (Function.update_of_ne hca (X6 a).tail X6).trans hX6c
  have hX6tgt : X6 tgt = Glyph.iend :: Gt := by
    rw [hX6, Function.update_of_ne htc (gEnd :: X2 c) X2, hX2,
      Function.update_self tgt (Glyph.iend :: X tgt) X, htgt]
  have hX7tgt : X7 tgt = Glyph.iend :: Gt :=
    (Function.update_of_ne hat' (X6 a).tail X6).trans hX6tgt
  have hX7tr : X7 tr = Gs' := by
    rw [hX7, Function.update_of_ne htra (X6 a).tail X6, hX6,
      Function.update_of_ne htrc (gEnd :: X2 c) X2, hX2,
      Function.update_of_ne httgt (Glyph.iend :: X tgt) X, htr]
  have hg8rT : g8 UR.rT = gTok := by
    rw [hg8, Function.update_self UR.rT gTok g7]
  have hg8rTok : g8 UR.rTok = gTok := by
    rw [hg8, Function.update_of_ne UR.rTok_ne_rT gTok g7, hg7,
      Function.update_of_ne UR.rTok_ne_rScr ((X6 a).headD .eos) g5, hg5,
      Function.update_of_ne UR.rTok_ne_rScr gEnd g4, hg4,
      Function.update_of_ne UR.rTok_ne_rPos Glyph.pos g3, hg3,
      Function.update_self UR.rTok gTok g1]
  obtain ⟨g9, X9, n9, h9ev, h9n, h9a, h9c, h9tgt, h9tr, h9fr⟩ :=
    UR.loop_eval main a tgt c tr hat hac hac' htc htt hct bs.reverse [] Gs (Glyph.iend :: Gt)
      Gc Gs' g8 X7 hX7a hX7c hX7tgt hX7tr hg8rT hg8rTok
  have h9n' : n9 ≤ 18 * ofBits bs + 18 * bs.length + 5 := by
    have h := h9n
    rw [List.length_reverse, UR.urW_reverse] at h
    rw [UR.urW_nil] at h
    simp only [Nat.mul_zero, Nat.zero_mul] at h
    omega
  have h9tgt' : X9 tgt = bs.map Glyph.bit ++ Glyph.iend :: Gt := by
    rw [h9tgt]; simp
  set g10 : Reg → Glyph := Function.update g9 UR.rPos Glyph.pos with hg10
  set X11 : Stk → List Glyph := Function.update X9 tgt (Glyph.pos :: X9 tgt) with hX11
  have f1 : Ev main (.set UR.rPos Glyph.pos) ⟨g9, X9⟩ ⟨g10, X9⟩ 1 := by
    rw [hg10]; exact ev_set' main UR.rPos Glyph.pos g9 X9
  have hg10rPos : g10 UR.rPos = Glyph.pos := by
    rw [hg10]; exact Function.update_self UR.rPos Glyph.pos g9
  have f2 : Ev main (.push tgt UR.rPos) ⟨g10, X9⟩ ⟨g10, X11⟩ 1 := by
    have h := ev_push' main tgt UR.rPos g10 X9
    rw [hg10rPos] at h
    rw [hX11]
    exact h
  have f3 : Ev main .skip ⟨g10, X11⟩ ⟨g10, X11⟩ 1 := ev_skip main _
  have hmain : Ev main (UR.urProg a tgt c tr) ⟨g, X⟩ ⟨g10, X11⟩
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (n9 + (1 + (1 + 1))))))))))) :=
    Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 (Ev.seq e5 (Ev.seq e6 (Ev.seq e7
      (Ev.seq e8 (Ev.seq h9ev (Ev.seq f1 (Ev.seq f2 f3))))))))))
  refine ⟨⟨g10, X11⟩, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact (Function.update_of_ne hat (Glyph.pos :: X9 tgt) X9).trans h9a
  · refine (Function.update_self tgt (Glyph.pos :: X9 tgt) X9).trans ?_
    rw [h9tgt']
    simp [List.cons_append, List.append_assoc]
  · refine (Function.update_of_ne hctg (Glyph.pos :: X9 tgt) X9).trans ?_
    rw [h9c]
    simp [UR.urW]
  · exact (Function.update_of_ne httgt (Glyph.pos :: X9 tgt) X9).trans h9tr
  · intro k h1 h2 h3 h4
    have e1 : X7 k = X6 k := Function.update_of_ne h1 (X6 a).tail X6
    have e2 : X6 k = X2 k := Function.update_of_ne h3 (gEnd :: X2 c) X2
    have e3 : X2 k = X k := Function.update_of_ne h2 (Glyph.iend :: X tgt) X
    exact (Function.update_of_ne h2 (Glyph.pos :: X9 tgt) X9).trans
      ((h9fr k h1 h2 h3 h4).trans (e1.trans (e2.trans e3)))

end Work.IntLib
