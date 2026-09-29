import Mathlib
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.Layout.SB.Specs
import Submission.Work.IntLib.encodeNatBridge

namespace Work.SB

open HvdH
open Work.Layout

/-- The size of an integer value is `isz`. -/
theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  simpa [HvdH.vsz] using Work.IntLib.vsz_int z

/-- The sort-based `applyAlong` epilogue: move the working list aside, fetch the parked
`int B` and `int n` from stack 1, and put them back below the working list. -/
theorem epilogue : EpilogueSpec := by
  refine ⟨seqs [mvVal 0 2 3 4, mvVal 1 0 3 4, mvVal 1 0 3 4, mvVal 2 0 3 4], 32, ?_⟩
  intro main g X R T1 n B flat rest hX0 hX1
  -- step 1: park the working value `flat` on stack 2
  have hA : X 0 = flat.enc ++ (encs rest ++ R) := by rw [hX0, encs_cons_tk, List.append_assoc]
  obtain ⟨s1, N1, hE1, hN1, hs1_0, hs1_b, hs1_c, hs1_d, hs1_o⟩ :=
    mvVal_up (main := main) (g := g) (X := X) (v := flat) (A' := encs rest ++ R)
      (b := (2 : Stk)) (c := (3 : Stk)) (d := (4 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hA
  -- step 2: bring `int B` (top of stack 1) down to stack 0
  have hs1_1 : s1.stk 1 = (Val.int B).enc ++ ((Val.int n).enc ++ T1) := by
    rw [hs1_o 1 (by decide) (by decide) (by decide) (by decide), hX1, List.append_assoc]
  obtain ⟨s2, N2, hE2, hN2, hs2_1, hs2_0, hs2_c, hs2_d, hs2_o⟩ :=
    mvVal_down (main := main) (g := s1.reg) (X := s1.stk) (v := Val.int B)
      (A' := (Val.int n).enc ++ T1) (a := (1 : Stk)) (c := (3 : Stk)) (d := (4 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_1
  -- step 3: bring `int n` down to stack 0
  obtain ⟨s3, N3, hE3, hN3, hs3_1, hs3_0, hs3_c, hs3_d, hs3_o⟩ :=
    mvVal_down (main := main) (g := s2.reg) (X := s2.stk) (v := Val.int n)
      (A' := T1) (a := (1 : Stk)) (c := (3 : Stk)) (d := (4 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2_1
  -- step 4: bring the parked `flat` back on top
  have hs3_2 : s3.stk 2 = flat.enc ++ X 2 := by
    rw [hs3_o 2 (by decide) (by decide) (by decide) (by decide),
        hs2_o 2 (by decide) (by decide) (by decide) (by decide), hs1_b]
  obtain ⟨s4, N4, hE4, hN4, hs4_b, hs4_0, hs4_c, hs4_d, hs4_o⟩ :=
    mvVal_down (main := main) (g := s3.reg) (X := s3.stk) (v := flat) (A' := X 2)
      (a := (2 : Stk)) (c := (3 : Stk)) (d := (4 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs3_2
  refine ⟨s4, N1 + (N2 + (N3 + N4)), ?_, ?_, ?_, ?_, ?_⟩
  · exact Ev.seq hE1 (Ev.seq hE2 (Ev.seq hE3 hE4))
  · have h2 : N2 ≤ 16 * (isz (B : ℤ) + 1) := by rw [← vsz_int (B : ℤ)]; exact hN2
    have h3 : N3 ≤ 16 * (isz (n : ℤ) + 1) := by rw [← vsz_int (n : ℤ)]; exact hN3
    omega
  · -- stack 0
    rw [hs4_0, hs3_0, hs2_0, hs1_0]
    simp only [encs_cons_tk, List.append_assoc]
  · -- stack 1
    rw [hs4_o 1 (by decide) (by decide) (by decide) (by decide), hs3_1]
  · -- every other stack
    intro k hk0 hk1
    by_cases hk2 : k = 2
    · rw [hk2]; exact hs4_b
    by_cases hk3 : k = 3
    · rw [hk3, hs4_c, hs3_c, hs2_c, hs1_c]
    by_cases hk4 : k = 4
    · rw [hk4, hs4_d, hs3_d, hs2_d, hs1_d]
    · rw [hs4_o k hk0 hk2 hk3 hk4, hs3_o k hk0 hk1 hk3 hk4,
          hs2_o k hk0 hk1 hk3 hk4, hs1_o k hk0 hk2 hk3 hk4]

end Work.SB
