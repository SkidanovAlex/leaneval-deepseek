import Mathlib
import Submission.Work.MainP.labStepAux
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.IntLib.encodeNatBridge

namespace Work.MainP

/-- `mvVal 0 1 14 15` moves the top value of stack `0` (a copy of `int z`) to stack `1`,
prepending its encoding to the stack-1 payload.  In the `labStep` frame the value stack is
`int z :: int z :: A`; the moved copy is parked on stack 1 and the value stack keeps one copy. -/
theorem labStepSave (main : HvdH.Cmd) (S1 : List HvdH.Glyph) (A : List HvdH.Val) (z : ℤ) :
    Work.MainP.WordR1 main (Work.Layout.mvVal 0 1 14 15) S1 ((HvdH.Val.int z).enc ++ S1)
      (fun vs => vs = HvdH.Val.int z :: HvdH.Val.int z :: A)
      (fun _ out => out = HvdH.Val.int z :: A)
      (fun _ => 16 * (HvdH.isz z + 1)) := by
  have hvsz : HvdH.vsz (HvdH.Val.int z) = HvdH.isz z := Work.IntLib.vsz_int z
  intro vs hvs s R hs h1s
  subst hvs
  have hs' : s.stk 0
      = (HvdH.Val.int z).enc ++ ((HvdH.Val.int z).enc ++ (HvdH.encs A ++ R)) := by
    rw [hs]
    simp [HvdH.encs, List.append_assoc]
  obtain ⟨s', n, hEv, hcost, h0, h1, h14, h15, hfr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 14) (d := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := HvdH.Val.int z)
      (A := (HvdH.Val.int z).enc ++ (HvdH.encs A ++ R)) (B := S1) hs' h1s
  obtain ⟨n', hEval, hn'⟩ := hEv
  refine ⟨HvdH.Val.int z :: A, s', n', rfl, hEval, ?_, ?_, ?_, ?_⟩
  · show n' ≤ 16 * (HvdH.isz z + 1)
    rw [hvsz] at hcost
    omega
  · rw [h0]
    simp [HvdH.encs, List.append_assoc]
  · exact h1
  · intro k hk0 hk1
    by_cases hc14 : k = 14
    · subst hc14; exact h14
    · by_cases hc15 : k = 15
      · subst hc15; exact h15
      · exact hfr k hk0 hk1 hc14 hc15

end Work.MainP
