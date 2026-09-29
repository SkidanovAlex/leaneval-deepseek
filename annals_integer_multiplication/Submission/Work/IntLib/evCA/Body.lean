import Mathlib
import Submission.Work.IntLib.evCarryDefs
import Submission.Work.IntLib.Shift.Loop
import Submission.Work.IntLib.evCA.stepAEv
import Submission.Work.IntLib.evCA.routeAEv
import Submission.Work.IntLib.evCA.flagAEv

/-!
# `evCarryAdd`: one iteration of the addition loop

`EvC.bodyA_ev` composes the three parts of the loop body (`stepA`, `routeA`, `flagA`) into a single
step of the invariant `EvC.addP`: from `addP k` (with `k < addN`) to `addP (k+1)`, in at most
`23` steps (`12 + 6 + 5`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace EvC

open HvdH

theorem bodyA_ev (main : Cmd) (b : ℕ) (W hbits LO : List Bool) (X : Stk → List Glyph)
    (Ws Os Cs A2s Bs : List Glyph) (k : ℕ) (t : State)
    (hP : addP b W hbits LO X Ws Os Cs A2s Bs k t) (hk : k < addN W hbits) :
    ∃ s' n, Work.Layout.Ev main bodyA t s' n ∧ n ≤ 23 ∧
      addP b W hbits LO X Ws Os Cs A2s Bs (k + 1) s' := by
  obtain ⟨hstr, hacc, hfr, hKa, hLa⟩ := hP
  obtain ⟨hstrW, hstrB⟩ := hstr
  obtain ⟨haccO, hacc2, haccCW⟩ := hacc
  obtain ⟨s1, n1, hev1, hn1, hstr1, hSa1, hKa1, hfr1⟩ :=
    evCA.stepAEv main W hbits Ws Bs k t ⟨hstrW, hstrB⟩ hk hKa
  obtain ⟨m1, he1, hm1⟩ := hev1
  have hacc1 : accP b W hbits LO Os A2s Cs k s1 :=
    ⟨by rw [hfr1 aO (by decide) (by decide)]; exact haccO,
     by rw [hfr1 a2 (by decide) (by decide)]; exact hacc2,
     by rw [hfr1 aCW (by decide) (by decide)]; exact haccCW⟩
  obtain ⟨s2, n2, hev2, hn2, hacc2', hfr2⟩ :=
    evCA.routeAEv main b W hbits LO Os A2s Cs k s1 hacc1 hSa1
  obtain ⟨m2, he2, hm2⟩ := hev2
  have hstr2 : strP W hbits Ws Bs (k + 1) s2 :=
    ⟨by rw [hfr2 aW (by decide) (by decide) (by decide)]; exact hstr1.1,
     by rw [hfr2 aB (by decide) (by decide) (by decide)]; exact hstr1.2⟩
  obtain ⟨s3, n3, hev3, hn3, hLa3, hfr3⟩ :=
    evCA.flagAEv main W hbits Ws Bs (k + 1) s2 hstr2 (by omega)
  obtain ⟨m3, he3, hm3⟩ := hev3
  have hKa2 : s2.reg rKa = s1.reg rKa :=
    Shift.Eval_reg_frame he2 (by decide : rKa ∉ Shift.cmdRegs routeA)
  have hKa3 : s3.reg rKa = s2.reg rKa :=
    Shift.Eval_reg_frame he3 (by decide : rKa ∉ Shift.cmdRegs flagA)
  have hstr3 : strP W hbits Ws Bs (k + 1) s3 :=
    ⟨by rw [hfr3 aW]; exact hstr2.1, by rw [hfr3 aB]; exact hstr2.2⟩
  have hacc3 : accP b W hbits LO Os A2s Cs (k + 1) s3 :=
    ⟨by rw [hfr3 aO]; exact hacc2'.1,
     by rw [hfr3 a2]; exact hacc2'.2.1,
     by rw [hfr3 aCW]; exact hacc2'.2.2⟩
  refine ⟨s3, m1 + (m2 + m3),
    ⟨m1 + (m2 + m3), HvdH.Eval.seq he1 (HvdH.Eval.seq he2 he3), ?_⟩, ?_, ?_⟩
  · omega
  · omega
  · refine ⟨hstr3, hacc3, ?_, ?_, hLa3⟩
    · intro j hj1 hj2 hj3 hj4 hj5
      rw [hfr3 j, hfr2 j hj3 hj4 hj5, hfr1 j hj1 hj2]
      exact hfr j hj1 hj2 hj3 hj4 hj5
    · rw [hKa3, hKa2, hKa1]
      rfl

end EvC
end Work.IntLib
