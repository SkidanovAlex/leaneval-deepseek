import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `Work.SynFFT.reorderWord`: the parameter-shuffling word of the top level

`ReorderProp` asks for a word that turns the stack

`int p :: int r :: intList ts :: int sgn :: rarrVal us :: rest`

into

`rarrVal us :: intList ts :: int sgn :: int r :: int p :: rest`

at cost `O(D · (vsz (rarrVal us) + vsz (intList ts) + isz p + isz r + isz sgn))`.

The word is four `KLib.roll`s, `roll 1 ; roll 3 ; roll 3 ; roll 4`, applied to the
five-element list `[A, B, C, D, E]` (where `A = int p`, `B = int r`, `C = intList ts`,
`D = int sgn`, `E = rarrVal us`):

* `roll 1 : [A,B,C,D,E] ↦ [B,A,C,D,E]`
* `roll 3 : [B,A,C,D,E] ↦ [D,B,A,C,E]`
* `roll 3 : [D,B,A,C,E] ↦ [C,D,B,A,E]`
* `roll 4 : [C,D,B,A,E] ↦ [E,C,D,B,A]`

Each `roll k` costs `Kr · (k+1) · (Σ_{i≤k} vsz vᵢ + 1) ≤ Kr · 5 · (S + 1)` where `S` is the
total size of the five parameters, so the four steps together cost at most
`4 · Kr · 5 · (S+1) = 20 · Kr · (S+1) ≤ Kr · (D+1) · (S+3)`, since `D + 1 = 1730 ≥ 20`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

namespace ReorderKit

/-- The cost of one `roll` with index at most `5` is at most `Kr * 5 * (S + 1)` whenever the
size of the inspected prefix is at most `S`. -/
theorem cost_le_of_sum_le (Kr k s S : ℕ) (hk : k ≤ 5) (h : s ≤ S) :
    Kr * k * (s + 1) ≤ Kr * 5 * (S + 1) := by
  have h1 : s + 1 ≤ S + 1 := by omega
  have h2 : k * (s + 1) ≤ 5 * (S + 1) := Nat.mul_le_mul hk h1
  calc Kr * k * (s + 1) = Kr * (k * (s + 1)) := by ring
    _ ≤ Kr * (5 * (S + 1)) := Nat.mul_le_mul_left Kr h2
    _ = Kr * 5 * (S + 1) := by ring

/-- Size sum of the first two values of a `cons`-chain. -/
theorem sum_take2_cons (x1 x2 : Val) (t : List Val) :
    (((x1 :: x2 :: t).take 2).map vsz).sum = vsz x1 + vsz x2 := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- Size sum of the first four values of a `cons`-chain. -/
theorem sum_take4_cons (x1 x2 x3 x4 : Val) (t : List Val) :
    (((x1 :: x2 :: x3 :: x4 :: t).take 4).map vsz).sum
      = vsz x1 + (vsz x2 + (vsz x3 + vsz x4)) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- Size sum of the first five values of a `cons`-chain. -/
theorem sum_take5_cons (x1 x2 x3 x4 x5 : Val) (t : List Val) :
    (((x1 :: x2 :: x3 :: x4 :: x5 :: t).take 5).map vsz).sum
      = vsz x1 + (vsz x2 + (vsz x3 + (vsz x4 + vsz x5))) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- One `roll k` step, stated with an explicit input list `A` and an explicit output list `A'`. -/
theorem rollStep' {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (h : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (k : ℕ) (A A' : List Val) (hk : k < A.length) (hA : A' = A.getD k .nil :: A.eraseIdx k)
    (Bd : ℕ) (hBd : Kr * (k+1) * (((A.take (k+1)).map vsz).sum + 1) ≤ Bd) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = A') (fun _ => Bd) := by
  refine MrgKit.WordR_weaken (MrgKit.rollStep h k A hk Bd hBd) (fun vs hvs => hvs) ?_
    (fun vs _ => le_rfl)
  intro vs out _ hout
  rw [hout, hA]

end ReorderKit

theorem reorderWord (hk : Work.SynFFT.KLib) : Work.SynFFT.ReorderProp := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  refine ⟨rollP 1 ;;; rollP 3 ;;; rollP 3 ;;; rollP 4, Kr, ?_⟩
  intro main p r ts sgn us rest
  let A0 : List Val := .int (p : ℤ) :: .int (r : ℤ) :: intList ts :: .int sgn :: rarrVal us :: rest
  let A1 : List Val := .int (r : ℤ) :: .int (p : ℤ) :: intList ts :: .int sgn :: rarrVal us :: rest
  let A2 : List Val := .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: intList ts :: rarrVal us :: rest
  let A3 : List Val := intList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rarrVal us :: rest
  let A4 : List Val := rarrVal us :: intList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest
  let S : ℕ := isz (p : ℤ) + isz (r : ℤ) + vsz (intList ts) + isz sgn + vsz (rarrVal us)
  let Bd : ℕ := Kr * 5 * (S + 1)
  have hS : Bd = Kr * 5 * (S + 1) := rfl
  -- ### step 1: `roll 1`, `[A,B,C,D,E] ↦ [B,A,C,D,E]`
  have s1 : WordR main (rollP 1) (fun vs => vs = A0) (fun _ out => out = A1) (fun _ => Bd) := by
    refine ReorderKit.rollStep' (hroll main) 1 A0 A1 (by simp [A0]) ?_ Bd ?_
    · dsimp only [A0, A1]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero]
    · have hsum : (((A0.take 2).map vsz).sum) ≤ S := by
        dsimp only [A0, S]
        simp only [ReorderKit.sum_take2_cons, MrgKit.vsz_int']
        omega
      have h := ReorderKit.cost_le_of_sum_le Kr 2 (((A0.take 2).map vsz).sum) S (by norm_num) hsum
      rw [hS]; exact h
  -- ### step 2: `roll 3`, `[B,A,C,D,E] ↦ [D,B,A,C,E]`
  have s2 : WordR main (rollP 3) (fun vs => vs = A1) (fun _ out => out = A2) (fun _ => Bd) := by
    refine ReorderKit.rollStep' (hroll main) 3 A1 A2 (by simp [A1]) ?_ Bd ?_
    · dsimp only [A1, A2]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero]
    · have hsum : (((A1.take 4).map vsz).sum) ≤ S := by
        dsimp only [A1, S]
        simp only [ReorderKit.sum_take4_cons, MrgKit.vsz_int']
        omega
      have h := ReorderKit.cost_le_of_sum_le Kr 4 (((A1.take 4).map vsz).sum) S (by norm_num) hsum
      rw [hS]; exact h
  -- ### step 3: `roll 3`, `[D,B,A,C,E] ↦ [C,D,B,A,E]`
  have s3 : WordR main (rollP 3) (fun vs => vs = A2) (fun _ out => out = A3) (fun _ => Bd) := by
    refine ReorderKit.rollStep' (hroll main) 3 A2 A3 (by simp [A2]) ?_ Bd ?_
    · dsimp only [A2, A3]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero]
    · have hsum : (((A2.take 4).map vsz).sum) ≤ S := by
        dsimp only [A2, S]
        simp only [ReorderKit.sum_take4_cons, MrgKit.vsz_int']
        omega
      have h := ReorderKit.cost_le_of_sum_le Kr 4 (((A2.take 4).map vsz).sum) S (by norm_num) hsum
      rw [hS]; exact h
  -- ### step 4: `roll 4`, `[C,D,B,A,E] ↦ [E,C,D,B,A]`
  have s4 : WordR main (rollP 4) (fun vs => vs = A3) (fun _ out => out = A4) (fun _ => Bd) := by
    refine ReorderKit.rollStep' (hroll main) 4 A3 A4 (by simp [A3]) ?_ Bd ?_
    · dsimp only [A3, A4]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero]
    · have hsum : (((A3.take 5).map vsz).sum) ≤ S := by
        dsimp only [A3, S]
        simp only [ReorderKit.sum_take5_cons, MrgKit.vsz_int']
        omega
      have h := ReorderKit.cost_le_of_sum_le Kr 5 (((A3.take 5).map vsz).sum) S (by norm_num) hsum
      rw [hS]; exact h
  -- ### assembly of the four steps
  have s34 := MrgKit.WordR_seqC s3 s4
  have s234 := MrgKit.WordR_seqC s2 s34
  have s1234 := MrgKit.WordR_seqC s1 s234
  refine MrgKit.WordR_weaken s1234 ?_ ?_ ?_
  · intro vs hvs; rw [hvs]
  · intro vs out _ hout; rw [hout]
  · intro vs _
    have hS3 : vsz (rarrVal us) + vsz (intList ts) + isz (p : ℤ) + isz (r : ℤ) + isz sgn + 3
        = S + 3 := by
      dsimp only [S]; omega
    have h4 : Bd + (Bd + (Bd + Bd)) = Kr * 20 * (S + 1) := by
      rw [hS]; ring
    have hD1 : D + 1 = 1730 := rfl
    rw [hS3, hD1, h4]
    have h20 : 20 * (S + 1) ≤ 1730 * (S + 3) := by omega
    calc Kr * 20 * (S + 1) = Kr * (20 * (S + 1)) := by ring
      _ ≤ Kr * (1730 * (S + 3)) := Nat.mul_le_mul_left Kr h20
      _ = Kr * 1730 * (S + 3) := by ring

end Work.SynFFT
