import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.hasSplitWord
import Submission.Work.SynFFT.hasScaleWord

/-!
# SynFFT: `HasYMulShift` — the signed cyclic-shift word

`Work.SynFFT.HasYMulShift` (kit2) asks for one `StackLang` word with

  `cvecVal w :: int s :: int sg :: int r :: int p :: rest`
  ↦
  `cvecVal (yMulS r s sg w) :: int s :: int sg :: int r :: int p :: rest`

for `w.length = r`, `s ≤ r`, `sg = ±1` and every coefficient of `w` in the disc, at cost
`O(r·p)` — the cheap form of the `y`-multiplication used by the synthetic FFT (a *signed
cyclic shift* of the coefficient vector, `kit2.yMulS`), as opposed to `kit.HasYMul`, which must
compute `(-e) fmod r` inside the word and therefore costs `O(r·p) + O(p²)`.

## The program

`yMulS r s sg w = (w.drop s).map (sg·) ++ (w.take s).map ((-sg)·)`, so the word

1. splits `cvecVal w` at `s` into `ofList ((w.map cfxVal).take s)` and
   `ofList ((w.map cfxVal).drop s)` (delegated `hasSplitWord`),
2. makes a copy of `int sg` and negates it,
3. scales both halves by their sign (delegated `hasScaleWord`, i.e. `mapList` with a per-element
   word), the take-half with `-sg` and the drop-half with `sg`,
4. concatenates them in the order `drop ++ take` (`LayoutLib.append`), and
5. cleans the scratch copies off the stack.

Seventeen library words, each `O(r·p)`; the size bookkeeping is done once, with
`MB = 20·(r+1)·(p+1)` a bound for the `vsz` of every value of every intermediate stack.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit

local infixl:68 " ;;; " => HvdH.Cmd.seq

lemma vsz_int_nat (n : ℕ) : vsz (.int (n : ℤ)) = n.size + 2 := by
  rw [vsz_int']
  simp only [isz]
  rw [show (n : ℤ).natAbs = n by simp]

lemma vsz_int_le_nat (n : ℕ) : vsz (.int (n : ℤ)) ≤ 3 * (n + 1) := by
  rw [vsz_int_nat]
  have h := size_le_three n
  omega

lemma vsz_int_le_of_le {n m : ℕ} (h : n ≤ m) : vsz (.int (n : ℤ)) ≤ 3 * (m + 1) := by
  rw [vsz_int_nat]
  have h2 : n.size ≤ m.size := Nat.size_le_size h
  have h3 := size_le_three m
  omega


/-- The assembly of `HasYMulShift` from the two delegated words (split, scale). -/
theorem mainAssembly
    (hk : KLib) (hi : IntLib) (hl : LayoutLib)
    (sp : Cmd) (Ks : ℕ)
    (hsp : ∀ (main : Cmd) (s : ℕ) (xs : List Val) (rest : List Val),
      WordR main sp
        (fun vs => vs = ofList xs :: .int (s : ℤ) :: rest)
        (fun vs out => out = ofList (xs.take s) :: ofList (xs.drop s) :: .int (s : ℤ) :: rest)
        (fun _ => Ks * (vsz (ofList xs) + isz (s : ℤ) + 1)))
    (mp : Cmd) (Km : ℕ)
    (hmp : ∀ (main : Cmd) (p : ℕ) (m : ℤ) (w : List (ℤ × ℤ)) (rest : List Val),
      (∀ z ∈ w, inDisc p z) → (m = 1 ∨ m = -1) → rest.getD 0 .nil = .int m →
      WordR main mp
        (fun vs => vs = cvecVal w :: rest)
        (fun vs out => out = cvecVal (w.map (fun z => (m * z.1, m * z.2))) :: rest)
        (fun _ => Km * (w.length + 1) * (p + 1)))
    : HasYMulShift := by
  unfold HasYMulShift
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨negP, Kn, hneg⟩ := hi.neg
  obtain ⟨appP, Kap, happ⟩ := hl.append
  set Kx : ℕ := Ks + Km + Kp + Kr + Ksw + Kd + Kdr + Kn + Kap + 1 with hKx
  refine ⟨sp ;;; pickP 3 ;;; dupP ;;; negP ;;; rollP 2 ;;; mp ;;; rollP 3 ;;; rollP 3 ;;;
    swapP ;;; mp ;;; rollP 2 ;;; swapP ;;; appP ;;; rollP 2 ;;; kdrP ;;; rollP 1 ;;; kdrP,
    1000000000 * Kx, ?_⟩
  intro main p r s sg w rest hwlen hsle hsg hdisc
  -- ## arithmetic
  have hKs : Ks ≤ Kx := by rw [hKx]; omega
  have hKm : Km ≤ Kx := by rw [hKx]; omega
  have hKp : Kp ≤ Kx := by rw [hKx]; omega
  have hKr : Kr ≤ Kx := by rw [hKx]; omega
  have hKsw : Ksw ≤ Kx := by rw [hKx]; omega
  have hKd : Kd ≤ Kx := by rw [hKx]; omega
  have hKdr : Kdr ≤ Kx := by rw [hKx]; omega
  have hKn : Kn ≤ Kx := by rw [hKx]; omega
  have hKap : Kap ≤ Kx := by rw [hKx]; omega
  set rp : ℕ := (r + 1) * (p + 1) with hrp
  set MB : ℕ := 20 * rp with hMB
  set Cs : ℕ := 10000000 * Kx * rp with hCs
  have hrp1 : 1 ≤ rp := by rw [hrp]; nlinarith [Nat.zero_le r, Nat.zero_le p]
  have hMB1 : 1 ≤ MB := by rw [hMB]; nlinarith
  have bd : ∀ Ki x : ℕ, Ki ≤ Kx → x ≤ 1000 * MB → Ki * x ≤ Cs := by
    intro Ki x h1 h2
    have h3 : x ≤ 1000000 * rp := by rw [hMB] at h2; nlinarith
    rw [hCs]
    calc Ki * x ≤ Kx * (1000000 * rp) := Nat.mul_le_mul h1 h3
      _ = 1000000 * Kx * rp := by ring
      _ ≤ 10000000 * Kx * rp := by nlinarith [Nat.zero_le Kx, Nat.zero_le rp]
  have bdR : ∀ K k x : ℕ, K ≤ Kx → (k + 1) * x ≤ 1000 * MB → K * (k + 1) * x ≤ Cs := by
    intro K k x hK hx
    rw [Nat.mul_assoc]
    exact bd K ((k + 1) * x) hK hx
  have bdS : ∀ K a b : ℕ, K ≤ Kx → (a + 1) * (b + 1) ≤ rp → K * (a + 1) * (b + 1) ≤ Cs := by
    intro K a b hK hab
    rw [Nat.mul_assoc]
    refine bd K ((a + 1) * (b + 1)) hK ?_
    rw [hMB]
    nlinarith [hab, hrp1]
  -- ## size bounds (for every value of every intermediate stack)
  have hbW : vsz (ofList (w.map cfxVal)) ≤ MB := by
    have h := vsz_cvecVal_le p r w hwlen hdisc
    have h2 : 13 * (r + 1) * (p + 1) ≤ MB := by rw [hMB, hrp]; nlinarith
    exact le_trans h h2
  have hbT : vsz (ofList ((w.map cfxVal).take s)) ≤ MB := by
    have h : vsz (ofList ((w.map cfxVal).take s)) ≤ r * (2 * p + 7 + 1) + 1 := by
      refine vsz_ofList_le_of_bound _ (2 * p + 7) r ?_ ?_
      · intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
        exact vsz_cfxVal_le p z (hdisc z hz)
      · rw [List.length_take, List.length_map, hwlen]
        omega
    have h2 : r * (2 * p + 7 + 1) + 1 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbD : vsz (ofList ((w.map cfxVal).drop s)) ≤ MB := by
    have h : vsz (ofList ((w.map cfxVal).drop s)) ≤ r * (2 * p + 7 + 1) + 1 := by
      refine vsz_ofList_le_of_bound _ (2 * p + 7) r ?_ ?_
      · intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hv)
        exact vsz_cfxVal_le p z (hdisc z hz)
      · rw [List.length_drop, List.length_map, hwlen]
        omega
    have h2 : r * (2 * p + 7 + 1) + 1 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbSv : vsz (.int (s : ℤ)) ≤ MB := by
    have h : vsz (.int (s : ℤ)) ≤ 3 * (r + 1) := vsz_int_le_of_le hsle
    have h2 : 3 * (r + 1) ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbGv : vsz (.int sg) ≤ MB := by
    have h : vsz (.int sg) ≤ 3 := by rcases hsg with h | h <;> rw [h] <;> decide
    have h2 : 3 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbRv : vsz (.int (r : ℤ)) ≤ MB := by
    have h : vsz (.int (r : ℤ)) ≤ 3 * (r + 1) := vsz_int_le_nat r
    have h2 : 3 * (r + 1) ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbPv : vsz (.int (p : ℤ)) ≤ MB := by
    have h : vsz (.int (p : ℤ)) ≤ 3 * (p + 1) := vsz_int_le_nat p
    have h2 : 3 * (p + 1) ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbSm : vsz (.int (-sg)) ≤ MB := by
    have h : vsz (.int (-sg)) ≤ 3 := by rcases hsg with h | h <;> rw [h] <;> decide
    have h2 : 3 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbTp : vsz (cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2)))) ≤ MB := by
    have hns : (-sg) = 1 ∨ (-sg) = -1 := by rcases hsg with h | h <;> simp [h]
    have h : vsz (cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2)))) ≤
        r * (2 * p + 7 + 1) + 1 := by
      refine vsz_ofList_le_of_bound _ (2 * p + 7) r ?_ ?_
      · intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact vsz_cfxVal_le p _ (inDisc_sign p z' (-sg) hns (hdisc z' (List.mem_of_mem_take hz')))
      · rw [List.length_map, List.length_map, List.length_take, hwlen]
        omega
    have h2 : r * (2 * p + 7 + 1) + 1 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbDp : vsz (cvecVal ((w.drop s).map (fun z => (sg * z.1, sg * z.2)))) ≤ MB := by
    have h : vsz (cvecVal ((w.drop s).map (fun z => (sg * z.1, sg * z.2)))) ≤
        r * (2 * p + 7 + 1) + 1 := by
      refine vsz_ofList_le_of_bound _ (2 * p + 7) r ?_ ?_
      · intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact vsz_cfxVal_le p _ (inDisc_sign p z' sg hsg (hdisc z' (List.mem_of_mem_drop hz')))
      · rw [List.length_map, List.length_map, List.length_drop, hwlen]
        omega
    have h2 : r * (2 * p + 7 + 1) + 1 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  have hbRL : vsz (ofList ((((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal)
      ++ (((w.take s).map (fun z => (-sg * z.1, -sg * z.2))).map cfxVal))) ≤ MB := by
    have hns : (-sg) = 1 ∨ (-sg) = -1 := by rcases hsg with h | h <;> simp [h]
    have h : vsz (ofList ((((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal)
        ++ (((w.take s).map (fun z => (-sg * z.1, -sg * z.2))).map cfxVal))) ≤
        r * (2 * p + 7 + 1) + 1 := by
      refine vsz_ofList_le_of_bound _ (2 * p + 7) r ?_ ?_
      · intro v hv
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
          obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
          exact vsz_cfxVal_le p _ (inDisc_sign p z' sg hsg (hdisc z' (List.mem_of_mem_drop hz')))
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
          obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
          exact vsz_cfxVal_le p _ (inDisc_sign p z' (-sg) hns (hdisc z' (List.mem_of_mem_take hz')))
      · simp only [List.length_append, List.length_map, List.length_drop, List.length_take]
        rw [hwlen]
        omega
    have h2 : r * (2 * p + 7 + 1) + 1 ≤ MB := by rw [hMB, hrp]; nlinarith
    linarith
  -- ## the states

  set A0 : List Val := cvecVal w :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA0
  set A1 : List Val := ofList ((w.map cfxVal).take s) :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA1
  set A2 : List Val := .int sg :: ofList ((w.map cfxVal).take s) :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA2
  set A3 : List Val := .int sg :: .int sg :: ofList ((w.map cfxVal).take s) :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA3
  set A4 : List Val := .int (-sg) :: .int sg :: ofList ((w.map cfxVal).take s) :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA4
  set A5 : List Val := ofList ((w.map cfxVal).take s) :: .int (-sg) :: .int sg :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA5
  set A6 : List Val := cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int sg :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA6
  set A7 : List Val := ofList ((w.map cfxVal).drop s) :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int sg :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA7
  set A8 : List Val := .int sg :: ofList ((w.map cfxVal).drop s) :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA8
  set A9 : List Val := ofList ((w.map cfxVal).drop s) :: .int sg :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA9
  set A10 : List Val := cvecVal ((w.drop s).map (fun z => (sg * z.1, sg * z.2))) :: .int sg :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA10
  set A11 : List Val := cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: cvecVal ((w.drop s).map (fun z => (sg * z.1, sg * z.2))) :: .int sg :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA11
  set A12 : List Val := cvecVal ((w.drop s).map (fun z => (sg * z.1, sg * z.2))) :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int sg :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA12
  set RL : List Val := (((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal) ++ (((w.take s).map (fun z => (-sg * z.1, -sg * z.2))).map cfxVal) with hRL
  set A13 : List Val := ofList RL :: .int sg :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA13
  set A14 : List Val := .int (-sg) :: ofList RL :: .int sg :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA14
  set A15 : List Val := ofList RL :: .int sg :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA15
  set A16 : List Val := .int sg :: ofList RL :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA16
  set A17 : List Val := ofList RL :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest with hA17
  -- ## the steps
  have s0 : WordR main sp (fun vs => vs = A0) (fun _ out => out = A1) (fun _ => Cs) := by
    refine WordR_conseqC (hsp main s (w.map cfxVal) (.int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest)) (by simp only [hA0, cvecVal])
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) (by
        have h1 : vsz (ofList (w.map cfxVal)) ≤ MB := hbW
        have h2 : isz (s : ℤ) ≤ MB := by rw [← vsz_int']; exact hbSv
        refine bd Ks (vsz (ofList (w.map cfxVal)) + isz (s : ℤ) + 1) hKs ?_
        nlinarith)
  have s1 : WordR main (pickP 3) (fun vs => vs = A1) (fun _ out => out = A2) (fun _ => Cs) := by
    refine WordR_conseqC (pickStep (hpick main) 3 A1 (by simp only [hA1]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kp 3 (((A1.take 4).map vsz).sum + 1) hKp ?_
        simp only [hA1]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbT, hbD, hbSv, hbGv, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s2 : WordR main dupP (fun vs => vs = A2) (fun _ out => out = A3) (fun _ => Cs) := by
    refine WordR_conseqC (dupStep (hdup main) (.int sg) A1 Cs (by
        refine bd Kd (vsz (.int sg) + 1) hKd ?_
        nlinarith [hbGv, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s3 : WordR main negP (fun vs => vs = A3) (fun _ out => out = A4) (fun _ => Cs) := by
    refine WordR_conseqC (negStep (hneg main) sg A2 Cs (by
        have h : isz sg ≤ 3 := by rcases hsg with h | h <;> rw [h] <;> decide
        refine bd Kn (isz sg) hKn ?_
        nlinarith [h, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s4 : WordR main (rollP 2) (fun vs => vs = A4) (fun _ out => out = A5) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 2 A4 (by simp only [hA4, hA2]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 2 (((A4.take 3).map vsz).sum + 1) hKr ?_
        simp only [hA4, hA2, hA1]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbSm, hbGv, hbT, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s5 : WordR main mp (fun vs => vs = A5) (fun _ out => out = A6) (fun _ => Cs) := by
    refine WordR_conseqC (hmp main p (-sg) (w.take s)
        (.int (-sg) :: .int sg :: ofList ((w.map cfxVal).drop s) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun z hz => hdisc z (List.mem_of_mem_take hz))
        (by rcases hsg with h | h <;> simp [h]) rfl) (by simp only [hA5, ← List.map_take, cvecVal])
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) (by
        refine bdS Km (w.take s).length p hKm ?_
        have h1 : (w.take s).length ≤ r := by rw [List.length_take, hwlen]; omega
        rw [hrp]
        nlinarith)
  have s6 : WordR main (rollP 3) (fun vs => vs = A6) (fun _ out => out = A7) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 3 A6 (by simp only [hA6]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 3 (((A6.take 4).map vsz).sum + 1) hKr ?_
        simp only [hA6]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbTp, hbSm, hbGv, hbD, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s7 : WordR main (rollP 3) (fun vs => vs = A7) (fun _ out => out = A8) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 3 A7 (by simp only [hA7]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 3 (((A7.take 4).map vsz).sum + 1) hKr ?_
        simp only [hA7]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbD, hbTp, hbSm, hbGv, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s8 : WordR main swapP (fun vs => vs = A8) (fun _ out => out = A9) (fun _ => Cs) := by
    refine WordR_conseqC (swapStep (hswap main) A8 (by simp only [hA8]; simp only [List.length_cons]; omega) Cs (by
        simp only [hA8]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        refine bd Ksw _ hKsw ?_
        nlinarith [hbGv, hbD, hbTp, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s9 : WordR main mp (fun vs => vs = A9) (fun _ out => out = A10) (fun _ => Cs) := by
    refine WordR_conseqC (hmp main p sg (w.drop s)
        (.int sg :: cvecVal ((w.take s).map (fun z => (-sg * z.1, -sg * z.2))) :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun z hz => hdisc z (List.mem_of_mem_drop hz)) hsg rfl) (by simp only [hA9, ← List.map_drop, cvecVal])
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) (by
        refine bdS Km (w.drop s).length p hKm ?_
        have h1 : (w.drop s).length ≤ r := by rw [List.length_drop, hwlen]; omega
        rw [hrp]
        nlinarith)
  have s10 : WordR main (rollP 2) (fun vs => vs = A10) (fun _ out => out = A11) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 2 A10 (by simp only [hA10]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 2 (((A10.take 3).map vsz).sum + 1) hKr ?_
        simp only [hA10]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbDp, hbGv, hbTp, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s11 : WordR main swapP (fun vs => vs = A11) (fun _ out => out = A12) (fun _ => Cs) := by
    refine WordR_conseqC (swapStep (hswap main) A11 (by simp only [hA11]; simp only [List.length_cons]; omega) Cs (by
        simp only [hA11]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        refine bd Ksw _ hKsw ?_
        nlinarith [hbTp, hbDp, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s12 : WordR main appP (fun vs => vs = A12) (fun _ out => out = A13) (fun _ => Cs) := by
    refine WordR_conseqC (appStep (happ main) (((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal)
        (((w.take s).map (fun z => (-sg * z.1, -sg * z.2))).map cfxVal)
        (.int sg :: .int (-sg) :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest) Cs (by
        have hb : vsz (ofList ((((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal))) ≤ MB := hbDp
        refine bd Kap (vsz (ofList ((((w.drop s).map (fun z => (sg * z.1, sg * z.2))).map cfxVal))) + 1) hKap ?_
        nlinarith [hb, hMB1])) (by simp only [hA12, cvecVal])
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s13 : WordR main (rollP 2) (fun vs => vs = A13) (fun _ out => out = A14) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 2 A13 (by simp only [hA13]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 2 (((A13.take 3).map vsz).sum + 1) hKr ?_
        simp only [hA13]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbRL, hbGv, hbSm, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s14 : WordR main kdrP (fun vs => vs = A14) (fun _ out => out = A15) (fun _ => Cs) := by
    refine WordR_conseqC (kdropStep (hkdr main) A14 (by simp only [hA14]; simp only [List.length_cons]; omega) Cs (by
        simp only [hA14]
        simp only [List.headD_cons]
        refine bd Kdr _ hKdr ?_
        nlinarith [hbSm, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s15 : WordR main (rollP 1) (fun vs => vs = A15) (fun _ out => out = A16) (fun _ => Cs) := by
    refine WordR_conseqC (rollStep (hroll main) 1 A15 (by simp only [hA15]; simp only [List.length_cons]; omega) Cs (by
        refine bdR Kr 1 (((A15.take 2).map vsz).sum + 1) hKr ?_
        simp only [hA15]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        nlinarith [hbRL, hbGv, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  have s16 : WordR main kdrP (fun vs => vs = A16) (fun _ out => out = A17) (fun _ => Cs) := by
    refine WordR_conseqC (kdropStep (hkdr main) A16 (by simp only [hA16]; simp only [List.length_cons]; omega) Cs (by
        simp only [hA16]
        simp only [List.headD_cons]
        refine bd Kdr _ hKdr ?_
        nlinarith [hbGv, hMB1])) (rfl)
      (fun out hout => by simp only [hout, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hRL, cvecVal, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.drop_succ_cons, List.drop_zero, List.headD_cons]) le_rfl
  -- ## the chain
  have e1 := WordR_seqC s0 s1
  have e2 := WordR_seqC e1 s2
  have e3 := WordR_seqC e2 s3
  have e4 := WordR_seqC e3 s4
  have e5 := WordR_seqC e4 s5
  have e6 := WordR_seqC e5 s6
  have e7 := WordR_seqC e6 s7
  have e8 := WordR_seqC e7 s8
  have e9 := WordR_seqC e8 s9
  have e10 := WordR_seqC e9 s10
  have e11 := WordR_seqC e10 s11
  have e12 := WordR_seqC e11 s12
  have e13 := WordR_seqC e12 s13
  have e14 := WordR_seqC e13 s14
  have e15 := WordR_seqC e14 s15
  have e16 := WordR_seqC e15 s16
  -- ## final
  refine WordR_weaken e16 (fun vs hvs => ?_) (fun vs out hvs hq => ?_) (fun vs hvs => ?_)
  · simp only [hvs, hA0, cvecVal]
  · rw [hq, hA17]
    have hRES' : ofList RL = cvecVal (yMulS r s sg w) := by
      simp only [hRL, ← List.map_append, yMulS, cvecVal]
    rw [hRES']
    exact ⟨yMulS r s sg w, rfl, rfl, yMulS_length sg hwlen, yMulS_inDisc hsg hdisc⟩
  · rw [hCs, hrp]
    nlinarith [Nat.zero_le Kx]

/-- `HasYMulShift`: the signed cyclic-shift word, assembled from the two delegated words. -/
theorem hasYMulShift (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hf : HvdH.FxLib) : Work.SynFFT.HasYMulShift := by
  obtain ⟨sp, Ks, hsp⟩ := hasSplitWord hk hl
  obtain ⟨mp, Km, hmp⟩ := hasScaleWord hk hi
  exact mainAssembly hk hi hl sp Ks hsp mp Km hmp

end Work.SynFFT
