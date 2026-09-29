import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `Work.SynFFT.hasSplitWord`

Split a list value at index `s`:

`ofList xs :: int s :: rest  ↦  ofList (xs.take s) :: ofList (xs.drop s) :: int s :: rest`,

at cost `K * (vsz (ofList xs) + isz s + 1)`.

The word is `pick 1 ; pick 1 ; pick 1 ; dropList ; roll 2 ; roll 2 ; takeList`.  Three
`pick 1` (copy the second value to the top) turn the stack

`ofList xs :: int s :: rest` into `int s :: ofList xs :: int s :: ofList xs :: int s :: rest`,

so that the layout word `LayoutLib.drop` (which consumes an `int k` above an `ofList xs`)
can split off `xs.drop s` while `int s`/`ofList xs` survive below; the two `roll 2` bring
that surviving pair back on top of the drop result, and `LayoutLib.take` (consuming the
pair) leaves `ofList (xs.take s)` above `xs.drop s`'s encoding and the original `int s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- Dropping entries of a list of values cannot increase the size of its encoding. -/
theorem vsz_ofList_drop_le (xs : List Val) (s : ℕ) : vsz (ofList (xs.drop s)) ≤ vsz (ofList xs) := by
  rw [MrgKit.vsz_ofList, MrgKit.vsz_ofList]
  have h1 : (xs.drop s).length ≤ xs.length := by simp
  have h2 : ((xs.drop s).map vsz).sum ≤ (xs.map vsz).sum := by
    have h := List.sum_take_add_sum_drop (xs.map vsz) s
    rw [← List.map_take, ← List.map_drop] at h
    omega
  omega

theorem hasSplitWord (hk : Work.SynFFT.KLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s : ℕ) (xs : List HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList xs :: HvdH.Val.int (s : ℤ) :: rest)
        (fun vs out => out = HvdH.ofList (xs.take s) :: HvdH.ofList (xs.drop s) :: HvdH.Val.int (s : ℤ) :: rest)
        (fun _ => K * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (s : ℤ) + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨ldrP, Kld, hldr⟩ := hl.drop
  obtain ⟨ltkP, Kt, hltk⟩ := hl.take
  refine ⟨pickP 1 ;;; pickP 1 ;;; pickP 1 ;;; ldrP ;;; rollP 2 ;;; rollP 2 ;;; ltkP,
    7 * (16 * (Kp + Kr + Kld + Kt + 1)), ?_⟩
  intro main s xs rest
  let Kx : ℕ := 16 * (Kp + Kr + Kld + Kt + 1)
  let V : ℕ := vsz (ofList xs) + isz (s : ℤ) + 1
  let Ds : ℕ := Kx * V
  have hKx : Kx = 16 * (Kp + Kr + Kld + Kt + 1) := rfl
  have hV : V = vsz (ofList xs) + isz (s : ℤ) + 1 := rfl
  have hDs : Ds = Kx * V := rfl
  have hKp : 2 * Kp ≤ Kx := by rw [hKx]; omega
  have hKr : 6 * Kr ≤ Kx := by rw [hKx]; omega
  have hKld : Kld ≤ Kx := by rw [hKx]; omega
  have hKt : Kt ≤ Kx := by rw [hKx]; omega
  have hdrop : vsz (ofList (xs.drop s)) ≤ vsz (ofList xs) := vsz_ofList_drop_le xs s
  -- ### step 1: copy `int s` to the top
  have e1 : WordR main (pickP 1)
      (fun vs => vs = ofList xs :: Val.int (s : ℤ) :: rest)
      (fun _ out => out = Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.pickStep (fun k => hpick main k) 1 (ofList xs :: Val.int (s : ℤ) :: rest) ?_ Ds ?_
    · simp
    · rw [hDs, hV]
      have hsum : (((ofList xs :: Val.int (s : ℤ) :: rest : List Val).take 2).map vsz).sum
          = vsz (ofList xs) + isz (s : ℤ) := by
        simp [MrgKit.vsz_int']
      rw [hsum]
      nlinarith [hKp]
  -- ### step 2: copy `ofList xs` to the top
  have e2 : WordR main (pickP 1)
      (fun vs => vs = Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest)
      (fun _ out => out = ofList xs :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.pickStep (fun k => hpick main k) 1
      (Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest) ?_ Ds ?_
    · simp
    · rw [hDs, hV]
      have hsum : (((Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest : List Val).take 2).map vsz).sum
          = isz (s : ℤ) + vsz (ofList xs) := by
        simp [MrgKit.vsz_int']
      rw [hsum]
      nlinarith [hKp]
  -- ### step 3: copy `int s` to the top again
  have e3 : WordR main (pickP 1)
      (fun vs => vs = ofList xs :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest)
      (fun _ out => out = Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: ofList xs ::
        Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.pickStep (fun k => hpick main k) 1
      (ofList xs :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest) ?_ Ds ?_
    · simp
    · rw [hDs, hV]
      have hsum : (((ofList xs :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest : List Val).take 2).map vsz).sum
          = vsz (ofList xs) + isz (s : ℤ) := by
        simp [MrgKit.vsz_int']
      rw [hsum]
      nlinarith [hKp]
  -- ### step 4: split off `xs.drop s`
  have e4 : WordR main ldrP
      (fun vs => vs = Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: ofList xs ::
        Val.int (s : ℤ) :: rest)
      (fun _ out => out = ofList (xs.drop s) :: Val.int (s : ℤ) :: ofList xs ::
        Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.layDropStep (fun k ys => hldr main k ys) s (s : ℤ) rfl xs
      (Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest) Ds ?_
    rw [hDs, hV]
    nlinarith [hKld]
  -- ### step 5: bring `ofList xs` back on top
  have e5 : WordR main (rollP 2)
      (fun vs => vs = ofList (xs.drop s) :: Val.int (s : ℤ) :: ofList xs ::
        Val.int (s : ℤ) :: rest)
      (fun _ out => out = ofList xs :: ofList (xs.drop s) :: Val.int (s : ℤ) ::
        Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.rollStep (fun k => hroll main k) 2
      (ofList (xs.drop s) :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest) ?_ Ds ?_
    · simp
    · rw [hDs, hV]
      have hsum : (((ofList (xs.drop s) :: Val.int (s : ℤ) :: ofList xs :: Val.int (s : ℤ) :: rest : List Val).take 3).map vsz).sum
          = vsz (ofList (xs.drop s)) + (isz (s : ℤ) + vsz (ofList xs)) := by
        simp [MrgKit.vsz_int']
      rw [hsum]
      nlinarith [hKr, hdrop]
  -- ### step 6: bring `int s` back on top
  have e6 : WordR main (rollP 2)
      (fun vs => vs = ofList xs :: ofList (xs.drop s) :: Val.int (s : ℤ) ::
        Val.int (s : ℤ) :: rest)
      (fun _ out => out = Val.int (s : ℤ) :: ofList xs :: ofList (xs.drop s) ::
        Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.rollStep (fun k => hroll main k) 2
      (ofList xs :: ofList (xs.drop s) :: Val.int (s : ℤ) :: Val.int (s : ℤ) :: rest) ?_ Ds ?_
    · simp
    · rw [hDs, hV]
      have hsum : (((ofList xs :: ofList (xs.drop s) :: Val.int (s : ℤ) :: Val.int (s : ℤ) :: rest : List Val).take 3).map vsz).sum
          = vsz (ofList xs) + (vsz (ofList (xs.drop s)) + isz (s : ℤ)) := by
        simp [MrgKit.vsz_int']
      rw [hsum]
      nlinarith [hKr, hdrop]
  -- ### step 7: split off `xs.take s`
  have e7 : WordR main ltkP
      (fun vs => vs = Val.int (s : ℤ) :: ofList xs :: ofList (xs.drop s) ::
        Val.int (s : ℤ) :: rest)
      (fun _ out => out = ofList (xs.take s) :: ofList (xs.drop s) :: Val.int (s : ℤ) :: rest)
      (fun _ => Ds) := by
    refine MrgKit.layTakeStep (fun k ys => hltk main k ys) s (s : ℤ) rfl xs
      (ofList (xs.drop s) :: Val.int (s : ℤ) :: rest) Ds ?_
    rw [hDs, hV]
    nlinarith [hKt]
  -- ### assembly
  have e67 := MrgKit.WordR_seqC e6 e7
  have e567 := MrgKit.WordR_seqC e5 e67
  have e4567 := MrgKit.WordR_seqC e4 e567
  have e34567 := MrgKit.WordR_seqC e3 e4567
  have e234567 := MrgKit.WordR_seqC e2 e34567
  have e1234567 := MrgKit.WordR_seqC e1 e234567
  refine MrgKit.WordR_weaken e1234567 (fun vs hvs => hvs) (fun vs out h1 h2 => ?_) (fun vs hvs => ?_)
  · rw [h2]
  · have h7 : Ds + (Ds + (Ds + (Ds + (Ds + (Ds + Ds))))) ≤ 7 * Ds := by omega
    have hKV : 7 * Ds ≤ (7 * (16 * (Kp + Kr + Kld + Kt + 1))) *
        (vsz (ofList xs) + isz (s : ℤ) + 1) := by
      have hEq : 7 * Ds = (7 * (16 * (Kp + Kr + Kld + Kt + 1))) *
          (vsz (ofList xs) + isz (s : ℤ) + 1) := by
        rw [hDs, hKx, hV]; ring
      exact le_of_eq hEq
    exact le_trans h7 hKV

end Work.SynFFT
