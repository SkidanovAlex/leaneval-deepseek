import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.ConvR.dropUnder
import Submission.Work.SB.BW2.dropTwoCostArith

/-!
# Dropping the two values just below the top of the value stack

The small `KernelLib` word behind `branchWord2`'s tail: from `a :: int B :: int A :: rest` it
produces `a :: rest`, i.e. it deletes the two integer values that sit *below* the top value `a`.

The word is the straight-line composition `roll 1, drop, roll 1, drop` of `KernelLib`:

* `roll 1` moves the second value `int B` to the front: `int B :: a :: int A :: rest`,
* `drop` deletes it: `a :: int A :: rest`,
* `roll 1` moves the second value `int A` to the front: `int A :: a :: rest`,
* `drop` deletes it: `a :: rest`.

Every `roll` only *moves* values (nothing is copied), so the running time is charged to the
sizes of the values that pass the front of the stack: if `vsz a ≤ 4·Bg` and
`isz B, isz A ≤ Ss`, the total cost is at most `(20·KR + 2·KD) · (Bg + Ss)` (see
`Work.SB.BW2.dropTwoCostArith` for the arithmetic).
-/

set_option autoImplicit false

namespace Work.SB.BW2

open HvdH

theorem dropTwoBelowWord (hK : HvdH.KernelLib) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a : HvdH.Val) (A B Bg Ss : ℕ)
        (rest : List HvdH.Val),
      1 ≤ Bg → HvdH.vsz a ≤ 4 * Bg → HvdH.isz (A : ℤ) ≤ Ss → HvdH.isz (B : ℤ) ≤ Ss →
      HvdH.WordR main p
        (fun vs => vs = a :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => out = a :: rest)
        (fun _ => K * (Bg + Ss)) := by
  obtain ⟨rollP, KR, hroll⟩ := hK.roll
  obtain ⟨dropP, KD, hdrop⟩ := hK.drop
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (rollP 1) dropP) (rollP 1)) dropP, 20 * KR + 2 * KD, ?_⟩
  intro main a A B Bg Ss rest hBg ha hA hB
  -- step 1: `roll 1`, bringing `int B` to the top
  have H1 : Work.ConvR.WordC main (rollP 1)
      (fun vs => vs = a :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest)
      (fun _ out => out = Val.int (B : ℤ) :: a :: Val.int (A : ℤ) :: rest)
      (2 * KR * (vsz a + isz (B : ℤ) + 1)) := by
    refine Work.ConvR.WordC.rollStep hK hroll (k := 1)
      (L := a :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest)
      (L' := Val.int (B : ℤ) :: a :: Val.int (A : ℤ) :: rest) ?_ ?_ ?_
    · simp
    · simp
    · have ht : (((a :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest).take (1 + 1)).map vsz).sum + 1
          = vsz a + isz (B : ℤ) + 1 := by
        simp [Work.ConvR.vsz_int, Nat.add_assoc]
      rw [ht]
      exact le_of_eq (by ring)
  -- step 2: `drop`, deleting `int B`
  have H2 : Work.ConvR.WordC main dropP
      (fun vs => vs = Val.int (B : ℤ) :: a :: Val.int (A : ℤ) :: rest)
      (fun _ out => out = a :: Val.int (A : ℤ) :: rest) (KD * (isz (B : ℤ) + 1)) := by
    refine Work.ConvR.WordC.dropStep hK hdrop
      (L := Val.int (B : ℤ) :: a :: Val.int (A : ℤ) :: rest)
      (L' := a :: Val.int (A : ℤ) :: rest) ?_ ?_ ?_
    · simp
    · rfl
    · show KD * (vsz (Val.int (B : ℤ)) + 1) ≤ KD * (isz (B : ℤ) + 1)
      simp [Work.ConvR.vsz_int]
  -- step 3: `roll 1`, bringing `int A` to the top
  have H3 : Work.ConvR.WordC main (rollP 1) (fun vs => vs = a :: Val.int (A : ℤ) :: rest)
      (fun _ out => out = Val.int (A : ℤ) :: a :: rest)
      (2 * KR * (vsz a + isz (A : ℤ) + 1)) := by
    refine Work.ConvR.WordC.rollStep hK hroll (k := 1)
      (L := a :: Val.int (A : ℤ) :: rest) (L' := Val.int (A : ℤ) :: a :: rest) ?_ ?_ ?_
    · simp
    · simp
    · have ht : (((a :: Val.int (A : ℤ) :: rest).take (1 + 1)).map vsz).sum + 1
          = vsz a + isz (A : ℤ) + 1 := by
        simp [Work.ConvR.vsz_int, Nat.add_assoc]
      rw [ht]
      exact le_of_eq (by ring)
  -- step 4: `drop`, deleting `int A`
  have H4 : Work.ConvR.WordC main dropP (fun vs => vs = Val.int (A : ℤ) :: a :: rest)
      (fun _ out => out = a :: rest) (KD * (isz (A : ℤ) + 1)) := by
    refine Work.ConvR.WordC.dropStep hK hdrop (L := Val.int (A : ℤ) :: a :: rest)
      (L' := a :: rest) ?_ ?_ ?_
    · simp
    · rfl
    · show KD * (vsz (Val.int (A : ℤ)) + 1) ≤ KD * (isz (A : ℤ) + 1)
      simp [Work.ConvR.vsz_int]
  -- the four steps in sequence, and the cost estimate
  exact Work.ConvR.WordC.toWordR (Work.ConvR.WordC.conseq hK
    (Work.ConvR.WordC.seqEq hK (Work.ConvR.WordC.seqEq hK (Work.ConvR.WordC.seqEq hK H1 H2) H3) H4)
    (fun _ h => h) (fun _ _ _ hout => hout)
    (dropTwoCostArith KR KD (vsz a) (isz (A : ℤ)) (isz (B : ℤ)) Bg Ss hBg ha hA hB))

end Work.SB.BW2
