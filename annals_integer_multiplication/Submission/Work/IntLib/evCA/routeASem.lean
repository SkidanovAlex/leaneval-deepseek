import Mathlib
import Submission.Work.IntLib.evCarryDefs

namespace Work.IntLib.evCA

open HvdH

theorem routeASem (main : HvdH.Cmd) (s : HvdH.State) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.routeA s s' n ∧ n ≤ 4 ∧
      ((s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos = Work.IntLib.gTok →
        s'.stk Work.IntLib.aO = s.reg Work.IntLib.EvC.rSa :: s.stk Work.IntLib.aO ∧
        s'.stk Work.IntLib.a2 = s.stk Work.IntLib.a2 ∧
        s'.stk Work.IntLib.aCW = (s.stk Work.IntLib.aCW).tail) ∧
      ((s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos ≠ Work.IntLib.gTok →
        s'.stk Work.IntLib.aO = s.stk Work.IntLib.aO ∧
        s'.stk Work.IntLib.a2 = s.reg Work.IntLib.EvC.rSa :: s.stk Work.IntLib.a2 ∧
        s'.stk Work.IntLib.aCW = s.stk Work.IntLib.aCW) ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aO → j ≠ Work.IntLib.a2 → j ≠ Work.IntLib.aCW →
        s'.stk j = s.stk j) := by
  let h : HvdH.Glyph := (s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos
  let s1 : HvdH.State := ⟨Function.update s.reg Work.IntLib.EvC.rTa h, s.stk⟩
  have hcond : s1.reg Work.IntLib.EvC.rTa = h := by
    dsimp only [s1]; rw [Function.update_self]
  have hpeek : Work.Layout.Ev main (.peek Work.IntLib.aCW Work.IntLib.EvC.rTa) s s1 1 :=
    Work.Layout.ev_peek main Work.IntLib.aCW Work.IntLib.EvC.rTa s
  by_cases htok : (s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos = Work.IntLib.gTok
  · let s2 : HvdH.State :=
      ⟨s1.reg, Function.update s1.stk Work.IntLib.aO (s1.reg Work.IntLib.EvC.rSa :: s1.stk Work.IntLib.aO)⟩
    let s3 : HvdH.State :=
      ⟨Function.update s2.reg Work.IntLib.EvC.rTa ((s2.stk Work.IntLib.aCW).headD HvdH.Glyph.eos),
        Function.update s2.stk Work.IntLib.aCW (s2.stk Work.IntLib.aCW).tail⟩
    have hpush : Work.Layout.Ev main (.push Work.IntLib.aO Work.IntLib.EvC.rSa) s1 s2 1 :=
      Work.Layout.ev_push main Work.IntLib.aO Work.IntLib.EvC.rSa s1
    have hpop : Work.Layout.Ev main (.pop Work.IntLib.aCW Work.IntLib.EvC.rTa) s2 s3 1 :=
      Work.Layout.ev_pop main Work.IntLib.aCW Work.IntLib.EvC.rTa s2
    have hseq : Work.Layout.Ev main
        (.seq (.push Work.IntLib.aO Work.IntLib.EvC.rSa) (.pop Work.IntLib.aCW Work.IntLib.EvC.rTa))
        s1 s3 2 :=
      Work.Layout.Ev.seq hpush hpop
    have hite : Work.Layout.Ev main
        (.ite Work.IntLib.EvC.rTa Work.IntLib.gTok
          (.seq (.push Work.IntLib.aO Work.IntLib.EvC.rSa) (.pop Work.IntLib.aCW Work.IntLib.EvC.rTa))
          (.push Work.IntLib.a2 Work.IntLib.EvC.rSa)) s1 s3 3 :=
      Work.Layout.Ev.iteT (by rw [hcond]; exact htok) hseq
    have hroute : Work.Layout.Ev main Work.IntLib.EvC.routeA s s3 4 :=
      Work.Layout.Ev.seq hpeek hite
    refine ⟨s3, 4, hroute, le_rfl, ?_, ?_, ?_⟩
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [s3, s2, s1]
        rw [Function.update_of_ne (by decide : Work.IntLib.aO ≠ Work.IntLib.aCW),
          Function.update_self,
          Function.update_of_ne (by decide : Work.IntLib.EvC.rSa ≠ Work.IntLib.EvC.rTa)]
      · dsimp only [s3, s2, s1]
        rw [Function.update_of_ne (by decide : Work.IntLib.a2 ≠ Work.IntLib.aCW),
          Function.update_of_ne (by decide : Work.IntLib.a2 ≠ Work.IntLib.aO)]
      · dsimp only [s3, s2, s1]
        rw [Function.update_self,
          Function.update_of_ne (by decide : Work.IntLib.aCW ≠ Work.IntLib.aO)]
    · intro hne; exact absurd htok hne
    · intro j hjO hj2 hjCW
      dsimp only [s3, s2, s1]
      rw [Function.update_of_ne hjCW, Function.update_of_ne hjO]
  · let s2 : HvdH.State :=
      ⟨s1.reg, Function.update s1.stk Work.IntLib.a2 (s1.reg Work.IntLib.EvC.rSa :: s1.stk Work.IntLib.a2)⟩
    have hpush : Work.Layout.Ev main (.push Work.IntLib.a2 Work.IntLib.EvC.rSa) s1 s2 1 :=
      Work.Layout.ev_push main Work.IntLib.a2 Work.IntLib.EvC.rSa s1
    have hite : Work.Layout.Ev main
        (.ite Work.IntLib.EvC.rTa Work.IntLib.gTok
          (.seq (.push Work.IntLib.aO Work.IntLib.EvC.rSa) (.pop Work.IntLib.aCW Work.IntLib.EvC.rTa))
          (.push Work.IntLib.a2 Work.IntLib.EvC.rSa)) s1 s2 2 :=
      Work.Layout.Ev.iteF (fun hh => htok (hcond.symm.trans hh)) hpush
    have hroute : Work.Layout.Ev main Work.IntLib.EvC.routeA s s2 3 :=
      Work.Layout.Ev.seq hpeek hite
    refine ⟨s2, 3, hroute, by omega, ?_, ?_, ?_⟩
    · intro hc; exact absurd hc htok
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [s2, s1]
        rw [Function.update_of_ne (by decide : Work.IntLib.aO ≠ Work.IntLib.a2)]
      · dsimp only [s2, s1]
        rw [Function.update_self,
          Function.update_of_ne (by decide : Work.IntLib.EvC.rSa ≠ Work.IntLib.EvC.rTa)]
      · dsimp only [s2, s1]
        rw [Function.update_of_ne (by decide : Work.IntLib.aCW ≠ Work.IntLib.a2)]
    · intro j hjO hj2 hjCW
      dsimp only [s2, s1]
      rw [Function.update_of_ne hj2]

end Work.IntLib.evCA
