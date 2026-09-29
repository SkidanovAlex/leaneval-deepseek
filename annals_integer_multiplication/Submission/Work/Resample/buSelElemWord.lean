import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWSelDefs
import Submission.Work.Resample.buSignElem

/-!
# `Work.Resample.buSelElemWord`: the per-element word of the `B̃` selection

`Work.Resample.buQWSelDefs` fixes the element map of the selection stage of the one-dimensional
`B̃` word (`paper Prop. 4.7(ii)`): from a keyed record `cons (int k) (cfxVal z)` it drops the key
and halves the fixed-point pair, i.e. it computes `Work.Resample.buSelElem` (`buSelElem_apply`).

This file proves that this map is computed by a StackLang word: from
`cons (int k) (cfxVal z) :: rest` it produces `cfxVal (buHalve z) :: rest` in `WordR`, at cost
`K * (isz k + isz z.1 + isz z.2 + 2)` --- exactly `K` times the encoding size of the input value.

The word is `uncons ; drop ; uncons ; (swap ; push 2 ; swap ; tdiv)² ; cons`, each of the twelve
steps costing at most one uniform budget `Kc * X` where `X = isz k + isz z.1 + isz z.2 + 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

namespace BuSelElem

open HvdH

/-- Every `isz z` is at least `2`. -/
theorem isz_ge_two (z : ℤ) : 2 ≤ isz z := by
  simp only [HvdH.isz]; omega

/-- Truncated halving does not increase the encoding size of an integer. -/
theorem isz_tdiv_two_le (a : ℤ) : isz (Int.tdiv a 2) ≤ isz a := by
  have h : (Int.tdiv a 2).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  have h2 : (Int.tdiv a 2).natAbs.size ≤ a.natAbs.size := Nat.size_le_size h
  simp only [HvdH.isz]; omega

/-- A step of cost `≤ Kc` fits in the uniform budget `Kc * X` (`X > 0`). -/
theorem le_mul_KcX {Kc X c : ℕ} (hc : c ≤ Kc) (hX : 0 < X) : c ≤ Kc * X :=
  le_trans hc (Nat.le_mul_of_pos_right Kc hX)

/-- `consV` as a `Wr` step with an arbitrary context below the two values. -/
theorem Wr.ofCons (KL : KernelLib) {main prog : Cmd} {K : ℕ} (a b : Val) {A : List Val}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b r, vs = a :: b :: r ∧ out = .cons a b :: r) (fun _ => K)) :
    Work.Resample.BuSign.Wr main prog (a :: b :: A) (.cons a b :: A) K := by
  intro rest
  refine KL.conseq main prog
    (fun vs => 2 ≤ vs.length)
    (fun vs : List Val => vs = (a :: b :: A) ++ rest)
    (fun vs out => ∃ a' b' r, vs = a' :: b' :: r ∧ out = .cons a' b' :: r)
    (fun _ out => out = (.cons a b :: A) ++ rest)
    (fun _ : List Val => K) (fun _ : List Val => K)
    h ?_ ?_ (fun _ _ => le_rfl)
  · intro vs hvs
    rw [hvs]; simp
  · intro vs out hvs ho
    obtain ⟨a', b', r, hvs', ho'⟩ := ho
    rw [hvs] at hvs'
    simp only [List.cons_append, List.cons.injEq] at hvs'
    obtain ⟨h1, h2, h3⟩ := hvs'
    subst h1; subst h2; subst h3
    rw [ho', List.cons_append]

/-- A `BinOp` as a `Wr` step with an arbitrary context below the two integer arguments. -/
theorem Wr.ofBinOpCtx (KL : KernelLib) {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main prog P f C) (a b : ℤ) (hb : P a b) (A : List Val) :
    Work.Resample.BuSign.Wr main prog ([.int a, .int b] ++ A) ([.int (f a b)] ++ A) (C a b) := by
  intro rest
  have h0 := Work.Resample.BuSign.Wr.ofBinOp (KL := KL) h a b hb (A ++ rest)
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using h0

end BuSelElem

open HvdH
open Work.Resample.BuSign
open Work.Resample.BuSelElem

theorem buSelElemWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (k : ℤ) (z : ℤ × ℤ) (rest : List HvdH.Val),
      HvdH.WordR main q
        (fun vs => vs = HvdH.Val.cons (HvdH.Val.int k) (HvdH.cfxVal z) :: rest)
        (fun vs out => vs = HvdH.Val.cons (HvdH.Val.int k) (HvdH.cfxVal z) :: rest ∧
          out = HvdH.cfxVal (Work.Resample.buHalve z) :: rest)
        (fun _ => K * (HvdH.isz k + HvdH.isz z.1 + HvdH.isz z.2 + 2)) := by
  obtain ⟨uProg, uK, uSpec⟩ := KL.unconsV
  obtain ⟨cProg, cK, cSpec⟩ := KL.consV
  obtain ⟨dProg, dK, dSpec⟩ := KL.drop
  obtain ⟨sProg, sK, sSpec⟩ := KL.swap
  obtain ⟨pvProg, pvK, pvSpec⟩ := KL.pushVal
  obtain ⟨tmProg, tmK, tmSpec⟩ := IL.tdiv
  set Kc : ℕ := 100 * (uK + cK + dK + sK + pvK + tmK + 1) with hKc
  let pv2 : Cmd := pvProg (.int (2 : ℤ))
  let prg : Cmd :=
    .seq uProg (.seq dProg (.seq uProg (.seq sProg (.seq pv2 (.seq sProg
      (.seq tmProg (.seq sProg (.seq pv2 (.seq sProg (.seq tmProg cProg))))))))))
  refine ⟨prg, 12 * Kc, ?_⟩
  intro main k z rest
  let Y : ℕ := Kc * (isz k + isz z.1 + isz z.2 + 2)
  have hXpos : 0 < isz k + isz z.1 + isz z.2 + 2 := by
    have h := isz_ge_two k; omega
  have hKcU : uK ≤ Kc := by rw [hKc]; omega
  have hKcC : cK ≤ Kc := by rw [hKc]; omega
  have hKcD : dK ≤ Kc := by rw [hKc]; omega
  have hKcS : sK ≤ Kc := by rw [hKc]; omega
  have hKcPv : pvK ≤ Kc := by rw [hKc]; omega
  have hKc4Tm : 4 * tmK ≤ Kc := by rw [hKc]; omega
  have hIsz2 : isz (2 : ℤ) = 4 := by decide
  have hVsz2 : vsz (.int (2 : ℤ)) = 4 := by rw [vsz_int_eq]; decide
  have h2k : 2 ≤ isz k := isz_ge_two k
  have h2z1 : 2 ≤ isz z.1 := isz_ge_two z.1
  have h2z2 : 2 ≤ isz z.2 := isz_ge_two z.2
  have hle_d : isz k + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_s1 : isz z.1 + isz z.2 + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_pv : 4 + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_s2 : 4 + isz z.2 + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_s3 : isz (Int.tdiv z.2 2) + isz z.1 + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by
    have h := isz_tdiv_two_le z.2; omega
  have hle_s4 : 4 + isz z.1 + 1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_t1 : isz z.2 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  have hle_t2 : isz z.1 ≤ isz k + isz z.1 + isz z.2 + 2 := by omega
  -- the twelve steps
  have hU1 : Wr main uProg [.cons (.int k) (cfxVal z)] [.int k, cfxVal z] Y :=
    Wr.mono (KL := KL) (Wr.ofUncons (KL := KL) (.int k) (cfxVal z) (A := []) (uSpec main))
      (by exact le_mul_KcX hKcU hXpos)
  have hD : Wr main dProg [.int k, cfxVal z] [cfxVal z] Y :=
    Wr.mono (KL := KL) (Wr.ofDrop (KL := KL) (v := .int k) (A := [cfxVal z]) (dSpec main))
      (by rw [vsz_int_eq]; exact Nat.mul_le_mul hKcD hle_d)
  have hU2 : Wr main uProg [cfxVal z] [.int z.1, .int z.2] Y :=
    Wr.mono (KL := KL) (Wr.ofUncons (KL := KL) (.int z.1) (.int z.2) (A := []) (uSpec main))
      (by exact le_mul_KcX hKcU hXpos)
  have hS1 : Wr main sProg [.int z.1, .int z.2] [.int z.2, .int z.1] Y :=
    Wr.mono (KL := KL) (Wr.ofSwap (KL := KL) (.int z.1) (.int z.2) (A := []) (sSpec main))
      (by rw [vsz_int_eq, vsz_int_eq]; exact Nat.mul_le_mul hKcS hle_s1)
  have hP1 : Wr main (pvProg (.int 2)) [.int z.2, .int z.1] [.int 2, .int z.2, .int z.1] Y :=
    Wr.mono (KL := KL) (Wr.ofPush (KL := KL) (A := [.int z.2, .int z.1]) (pvSpec main (.int 2)))
      (by rw [hVsz2]; exact Nat.mul_le_mul hKcPv hle_pv)
  have hS2 : Wr main sProg [.int 2, .int z.2, .int z.1] [.int z.2, .int 2, .int z.1] Y :=
    Wr.mono (KL := KL) (Wr.ofSwap (KL := KL) (.int 2) (.int z.2) (A := [.int z.1]) (sSpec main))
      (by rw [hVsz2, vsz_int_eq]; exact Nat.mul_le_mul hKcS hle_s2)
  have hT1 : Wr main tmProg [.int z.2, .int 2, .int z.1] [.int (Int.tdiv z.2 2), .int z.1] Y :=
    Wr.mono (KL := KL)
      (Wr.ofBinOpCtx (KL := KL) (tmSpec main) (z.2) 2 (by norm_num) [.int z.1])
      (by rw [hIsz2]
          calc tmK * isz z.2 * 4 = (4 * tmK) * isz z.2 := by ring
            _ ≤ Kc * (isz k + isz z.1 + isz z.2 + 2) := Nat.mul_le_mul hKc4Tm hle_t1)
  have hS3 : Wr main sProg [.int (Int.tdiv z.2 2), .int z.1] [.int z.1, .int (Int.tdiv z.2 2)] Y :=
    Wr.mono (KL := KL)
      (Wr.ofSwap (KL := KL) (.int (Int.tdiv z.2 2)) (.int z.1) (A := []) (sSpec main))
      (by rw [vsz_int_eq, vsz_int_eq]; exact Nat.mul_le_mul hKcS hle_s3)
  have hP2 : Wr main (pvProg (.int 2)) [.int z.1, .int (Int.tdiv z.2 2)]
      [.int 2, .int z.1, .int (Int.tdiv z.2 2)] Y :=
    Wr.mono (KL := KL)
      (Wr.ofPush (KL := KL) (A := [.int z.1, .int (Int.tdiv z.2 2)]) (pvSpec main (.int 2)))
      (by rw [hVsz2]; exact Nat.mul_le_mul hKcPv hle_pv)
  have hS4 : Wr main sProg [.int 2, .int z.1, .int (Int.tdiv z.2 2)]
      [.int z.1, .int 2, .int (Int.tdiv z.2 2)] Y :=
    Wr.mono (KL := KL)
      (Wr.ofSwap (KL := KL) (.int 2) (.int z.1) (A := [.int (Int.tdiv z.2 2)]) (sSpec main))
      (by rw [hVsz2, vsz_int_eq]; exact Nat.mul_le_mul hKcS hle_s4)
  have hT2 : Wr main tmProg [.int z.1, .int 2, .int (Int.tdiv z.2 2)]
      [.int (Int.tdiv z.1 2), .int (Int.tdiv z.2 2)] Y :=
    Wr.mono (KL := KL)
      (Wr.ofBinOpCtx (KL := KL) (tmSpec main) (z.1) 2 (by norm_num) [.int (Int.tdiv z.2 2)])
      (by rw [hIsz2]
          calc tmK * isz z.1 * 4 = (4 * tmK) * isz z.1 := by ring
            _ ≤ Kc * (isz k + isz z.1 + isz z.2 + 2) := Nat.mul_le_mul hKc4Tm hle_t2)
  have hC : Wr main cProg [.int (Int.tdiv z.1 2), .int (Int.tdiv z.2 2)]
      [.cons (.int (Int.tdiv z.1 2)) (.int (Int.tdiv z.2 2))] Y :=
    Wr.mono (KL := KL)
      (Wr.ofCons (KL := KL) (.int (Int.tdiv z.1 2)) (.int (Int.tdiv z.2 2)) (A := [])
        (cSpec main))
      (by exact le_mul_KcX hKcC hXpos)
  -- assembly
  have hAll : Wr main prg [.cons (.int k) (cfxVal z)]
      [.cons (.int (Int.tdiv z.1 2)) (.int (Int.tdiv z.2 2))] (12 * Y) :=
    Wr.mono (KL := KL)
      (Wr.comp KL hU1 (Wr.comp KL hD (Wr.comp KL hU2 (Wr.comp KL hS1 (Wr.comp KL hP1
        (Wr.comp KL hS2 (Wr.comp KL hT1 (Wr.comp KL hS3 (Wr.comp KL hP2
        (Wr.comp KL hS4 (Wr.comp KL hT2 hC)))))))))))
      (by omega)
  refine KL.conseq main prg
    (fun vs : List Val => vs = [.cons (.int k) (cfxVal z)] ++ rest)
    (fun vs : List Val => vs = .cons (.int k) (cfxVal z) :: rest)
    (fun _ out : List Val =>
      out = [.cons (.int (Int.tdiv z.1 2)) (.int (Int.tdiv z.2 2))] ++ rest)
    (fun vs out : List Val => vs = .cons (.int k) (cfxVal z) :: rest ∧
      out = cfxVal (buHalve z) :: rest)
    (fun _ : List Val => 12 * Y)
    (fun _ : List Val => (12 * Kc) * (isz k + isz z.1 + isz z.2 + 2))
    (hAll rest) ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs ho
    exact ⟨hvs, by rw [ho, List.cons_append]; rfl⟩
  · intro vs hvs
    exact le_of_eq (Nat.mul_assoc 12 Kc (isz k + isz z.1 + isz z.2 + 2)).symm

end Work.Resample
