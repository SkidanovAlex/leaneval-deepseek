import Mathlib
import Submission.Work.MainP.labStepAux
import Submission.Work.Layout.mvVal_ev_full

namespace Work.MainP

open HvdH

/-- `mvVal 1 0 14 15` pops the top value of stack 1 and pushes it on top of stack 0, leaving the
rest of stack 1 untouched.  Stated as a `WordR1` with stack-1 payload `(int z).enc ++ S1 ↦ S1`. -/
theorem labStepRestore (main : HvdH.Cmd) (S1 : List HvdH.Glyph) (A : List HvdH.Val) (z : ℤ) :
    Work.MainP.WordR1 main (Work.Layout.mvVal 1 0 14 15) ((HvdH.Val.int z).enc ++ S1) S1
      (fun vs => vs = A)
      (fun _ out => out = HvdH.Val.int z :: A)
      (fun _ => 16 * (HvdH.isz z + 1)) := by
  intro vs hvs s R hs h1s
  subst vs
  obtain ⟨s', n, hev, hcost, hpay, hb', hc', hd', hfr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 14) (d := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := HvdH.Val.int z) (A := S1) (B := HvdH.encs A ++ R) h1s hs
  obtain ⟨n₀, hev₀, hn₀⟩ := hev
  have hvsz : HvdH.vsz (HvdH.Val.int z) = HvdH.isz z := by simp
  have hcost' : n ≤ 16 * (HvdH.isz z + 1) := by rw [hvsz] at hcost; exact hcost
  refine ⟨HvdH.Val.int z :: A, s', n₀, rfl, hev₀, le_trans hn₀ hcost', ?_, hpay, ?_⟩
  · rw [hb']
    simp [HvdH.encs, List.append_assoc]
  · intro k hk0 hk1
    by_cases hk14 : k = 14
    · rw [hk14]; exact hc'
    by_cases hk15 : k = 15
    · rw [hk15]; exact hd'
    · exact hfr k hk1 hk0 hk14 hk15

end Work.MainP
