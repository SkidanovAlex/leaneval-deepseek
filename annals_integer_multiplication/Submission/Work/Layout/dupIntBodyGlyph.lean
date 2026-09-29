import Mathlib
import Submission.Work.Layout.dupIntDefs

namespace Work.Layout

open HvdH
open Work.Layout.Sk

/-- One iteration of the `dupInt` loop on a glyph `h` that is not the boundary marker: `h` is pushed
onto both `S` and `B` (so both stacks receive `h` on top), and the loop flag is set to `cons`. -/
theorem dupIntBodyGlyph {main : Cmd} {S B T : Stk} (hSB : S ≠ B) (hST : S ≠ T) (hBT : B ≠ T)
    {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph} {G C S0 B0 : List Glyph}
    (hh : h ≠ gMark) (hT : X T = h :: G ++ gMark :: C) (hS : X S = S0) (hB : X B = B0) :
    ∃ s' n, Ev main (Sk.dupIntBody S B T) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk S = h :: S0 ∧ s'.stk B = h :: B0 ∧ s'.stk T = G ++ gMark :: C ∧
      s'.reg Sk.rF = Glyph.cons := by
  -- `dupIntBody S B T` = `pop T rK ; if rK = gMark then set rF gMark else push S rK ; push B rK ; set rF cons`
  have hhead : (X T).headD Glyph.eos = h := by rw [hT]; rfl
  have htail : (X T).tail = G ++ gMark :: C := by rw [hT]; rfl
  -- the three intermediate states, one per primitive of the `else` branch
  let s1 : State := ⟨Function.update g Sk.rK h, Function.update X T (G ++ gMark :: C)⟩
  let s2 : State := ⟨s1.reg, Function.update s1.stk S (s1.reg Sk.rK :: s1.stk S)⟩
  let s3 : State := ⟨s2.reg, Function.update s2.stk B (s2.reg Sk.rK :: s2.stk B)⟩
  let s4 : State := ⟨Function.update s3.reg Sk.rF Glyph.cons, s3.stk⟩
  have e1 : Ev main (.pop T Sk.rK) ⟨g, X⟩ s1 1 := by
    have hp := ev_pop' main T Sk.rK g X
    rw [hhead, htail] at hp
    exact hp
  -- the popped glyph is `h`, so the `ite` takes the `else` branch
  have hne : s1.reg Sk.rK ≠ gMark := by
    simp only [s1, Function.update_self]
    exact hh
  have e2 : Ev main (.push S Sk.rK) s1 s2 1 := ev_push main S Sk.rK s1
  have e3 : Ev main (.push B Sk.rK) s2 s3 1 := ev_push main B Sk.rK s2
  have e4 : Ev main (.set Sk.rF Glyph.cons) s3 s4 1 := ev_set main Sk.rF Glyph.cons s3
  have e_rest : Ev main (.seq (.push B Sk.rK) (.set Sk.rF Glyph.cons)) s2 s4 2 :=
    Ev.seq' (C := 2) e3 e4 (by norm_num)
  have e_branch : Ev main
      (.seq (.push S Sk.rK) (.seq (.push B Sk.rK) (.set Sk.rF Glyph.cons))) s1 s4 3 :=
    Ev.seq' (C := 3) e2 e_rest (by norm_num)
  have e_ite : Ev main (.ite Sk.rK gMark (.set Sk.rF gMark)
      (.seq (.push S Sk.rK) (.seq (.push B Sk.rK) (.set Sk.rF Glyph.cons)))) s1 s4 4 :=
    Ev.iteF (C := 3) hne e_branch
  have e_all : Ev main (Sk.dupIntBody S B T) ⟨g, X⟩ s4 5 := by
    show Ev main (.seq (.pop T Sk.rK) (.ite Sk.rK gMark (.set Sk.rF gMark)
      (.seq (.push S Sk.rK) (.seq (.push B Sk.rK) (.set Sk.rF Glyph.cons))))) ⟨g, X⟩ s4 5
    exact Ev.seq' (C := 5) e1 e_ite (by norm_num)
  refine ⟨s4, 5, e_all, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp only [s4, s3, s2, s1]
    rw [Function.update_of_ne hSB, Function.update_self, Function.update_of_ne hST,
      Function.update_self, hS]
  · simp only [s4, s3, s2, s1]
    rw [Function.update_self, Function.update_of_ne hSB.symm, Function.update_of_ne hBT, hB,
      Function.update_self]
  · simp only [s4, s3, s2, s1]
    rw [Function.update_of_ne hBT.symm, Function.update_of_ne hST.symm, Function.update_self]
  · simp only [s4, Function.update_self]

end Work.Layout
