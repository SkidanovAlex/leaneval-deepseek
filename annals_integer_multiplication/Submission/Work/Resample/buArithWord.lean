import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buColsDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- A list of naturals all of whose entries are `≤ B` has sum `≤ length * B`. -/
private theorem sum_le_length_mul (l : List ℕ) : ∀ (B : ℕ), (∀ x ∈ l, x ≤ B) → l.sum ≤ l.length * B := by
  induction l with
  | nil => intro B _; simp
  | cons a t ih =>
    intro B h
    have ha : a ≤ B := h a (by simp)
    have ht : ∀ x ∈ t, x ≤ B := fun x hx => h x (by simp [hx])
    have ih' := ih B ht
    simp only [List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- The arithmetic element word: from the window `int i :: X :: buCB p α s t` it produces
`int (buHidx p α i) :: X :: buCB p α s t`, where `buHidx p α i = (1 - [i < m]) + (i - m)`,
`m = egM p α`.  The constants `X` and `N` bound the size of the extra value and of the integer
values involved.

Program: pick `m` (index 6), pick a copy of `i` (index 1), `lt` (flag `[i<m]`), push `1`,
`sub` (`1 - [i<m]`), `add` (with the surviving `i`), pick `m` again (index 6), `swap`,
`sub` (giving `((1-[i<m])+i) - m = buHidx p α i`). -/
theorem buArithWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (i : ℤ) (X : Val) (N : ℕ),
      vsz X ≤ N → isz i ≤ N → buSZ p ≤ N →
      Work.Resample.Pipe main prog (.int i :: X :: buCB p α s t)
        (.int (buHidx p α i) :: X :: buCB p α s t) (K * (N + 1)) := by
  obtain ⟨pickProg, Kp, hPk⟩ := KL.pick
  obtain ⟨swapProg, Ksw, hSw⟩ := KL.swap
  obtain ⟨pushProg, Kpu, hPush⟩ := KL.pushVal
  obtain ⟨ltProg, Klt, hLt⟩ := IL.lt
  obtain ⟨subProg, Ksu, hSu⟩ := IL.sub
  obtain ⟨addProg, Kad, hAd⟩ := IL.add
  refine ⟨Cmd.seq (pickProg 6) (Cmd.seq (pickProg 1) (Cmd.seq ltProg (Cmd.seq (pushProg (.int 1))
      (Cmd.seq subProg (Cmd.seq addProg (Cmd.seq (pickProg 6) (Cmd.seq swapProg subProg))))))),
    buArithK Kp Ksw Kpu Klt Ksu Kad, ?_⟩
  intro main p α s t hs hst hα hp htp hαp i X N hX hi hB
  let Bc : List Val := buCB p α s t
  let M : ℤ := (egM p α : ℤ)
  let U : ℤ := if i < (egM p α : ℤ) then (1 : ℤ) else 0
  let dl : ℤ := (1 - U) + i
  let W0 : List Val := .int i :: X :: Bc
  let W1 : List Val := .int M :: W0
  let W2 : List Val := .int i :: W1
  let W3 : List Val := .int U :: .int i :: X :: Bc
  let W4 : List Val := .int 1 :: W3
  let W5 : List Val := .int (1 - U) :: .int i :: X :: Bc
  let W6 : List Val := .int dl :: X :: Bc
  let W7 : List Val := .int M :: W6
  let W8 : List Val := .int dl :: .int M :: X :: Bc
  let W9 : List Val := .int (dl - M) :: X :: Bc
  have hN100 : 100 ≤ N := le_trans (by simp only [buSZ]; omega) hB
  have hM : isz M ≤ N := le_trans (isz_egM_le p α) hB
  have hBmem : ∀ v ∈ Bc, vsz v ≤ N :=
    fun v hv => le_trans (vsz_buCB_le hs hst hα hp htp hαp hv) hB
  have hU : isz U ≤ 3 := isz_ltFlag_le i M
  have h1z : isz (1 : ℤ) ≤ N := le_trans (isz_const_le_buSZ p 1 (by norm_num)) hB
  have h1U : isz (1 - U) ≤ N + 3 := by
    have h := isz_sub_le (1 : ℤ) U
    omega
  have hdl : isz dl ≤ 2 * N + 3 := by
    have h := isz_add_le_coord (1 - U) i
    dsimp only [dl]
    omega
  -- the sought value
  have hval : dl - M = buHidx p α i := by
    rw [buHidx_eq]
    dsimp only [dl, M, U]
    ring
  -- entry bounds
  have entryW0 : ∀ v ∈ W0, vsz v ≤ 2 * N + 3 := by
    intro v hv
    simp only [W0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | hv
    · rw [Work.Fx.vsz_int]; omega
    · omega
    · exact le_trans (hBmem v hv) (by omega)
  have entryW1 : ∀ v ∈ W1, vsz v ≤ 2 * N + 3 := by
    intro v hv
    simp only [W1, W0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | hv
    · rw [Work.Fx.vsz_int]; omega
    · rw [Work.Fx.vsz_int]; omega
    · omega
    · exact le_trans (hBmem v hv) (by omega)
  have entryW6 : ∀ v ∈ W6, vsz v ≤ 2 * N + 3 := by
    intro v hv
    simp only [W6, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | hv
    · rw [Work.Fx.vsz_int]; omega
    · omega
    · exact le_trans (hBmem v hv) (by omega)
  have hsl_le : ∀ (W : List Val) (k : ℕ), (∀ v ∈ W, vsz v ≤ 2 * N + 3) →
      Work.Fx.szl (W.take k) ≤ k * (2 * N + 3) := by
    intro W k h
    have h1 := szl_le_length_mul' (l := W.take k) (N := 2 * N + 3)
      (fun v hv => h v (List.mem_of_mem_take hv))
    have h2 : (W.take k).length ≤ k := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  -- the nine step costs, each `≤ 100 * Kᵢ * (N+1)`
  have c1 : Kp * 7 * (Work.Fx.szl (W0.take 7) + 1) ≤ 100 * Kp * (N + 1) := by
    have hs' := hsl_le W0 7 entryW0
    have h2 : 7 * (Work.Fx.szl (W0.take 7) + 1) ≤ 100 * (N + 1) := by omega
    calc Kp * 7 * (Work.Fx.szl (W0.take 7) + 1)
        = Kp * (7 * (Work.Fx.szl (W0.take 7) + 1)) := by ring
      _ ≤ Kp * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Kp * (N + 1) := by ring
  have c2 : Kp * 2 * (Work.Fx.szl (W1.take 2) + 1) ≤ 100 * Kp * (N + 1) := by
    have hs' := hsl_le W1 2 entryW1
    have h2 : 2 * (Work.Fx.szl (W1.take 2) + 1) ≤ 100 * (N + 1) := by omega
    calc Kp * 2 * (Work.Fx.szl (W1.take 2) + 1)
        = Kp * (2 * (Work.Fx.szl (W1.take 2) + 1)) := by ring
      _ ≤ Kp * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Kp * (N + 1) := by ring
  have c3 : Klt * (isz i + isz M) ≤ 100 * Klt * (N + 1) := by
    have h2 : isz i + isz M ≤ 100 * (N + 1) := by omega
    calc Klt * (isz i + isz M) ≤ Klt * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Klt * (N + 1) := by ring
  have c4 : Kpu * (vsz (.int 1) + 1) ≤ 100 * Kpu * (N + 1) := by
    have h2 : vsz (.int 1) + 1 ≤ 100 * (N + 1) := by
      rw [Work.Fx.vsz_int]; omega
    calc Kpu * (vsz (.int 1) + 1) ≤ Kpu * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Kpu * (N + 1) := by ring
  have c5 : Ksu * (isz (1 : ℤ) + isz U) ≤ 100 * Ksu * (N + 1) := by
    have h2 : isz (1 : ℤ) + isz U ≤ 100 * (N + 1) := by omega
    calc Ksu * (isz (1 : ℤ) + isz U) ≤ Ksu * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Ksu * (N + 1) := by ring
  have c6 : Kad * (isz (1 - U) + isz i) ≤ 100 * Kad * (N + 1) := by
    have h2 : isz (1 - U) + isz i ≤ 100 * (N + 1) := by omega
    calc Kad * (isz (1 - U) + isz i) ≤ Kad * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Kad * (N + 1) := by ring
  have c7 : Kp * 7 * (Work.Fx.szl (W6.take 7) + 1) ≤ 100 * Kp * (N + 1) := by
    have hs' := hsl_le W6 7 entryW6
    have h2 : 7 * (Work.Fx.szl (W6.take 7) + 1) ≤ 100 * (N + 1) := by omega
    calc Kp * 7 * (Work.Fx.szl (W6.take 7) + 1)
        = Kp * (7 * (Work.Fx.szl (W6.take 7) + 1)) := by ring
      _ ≤ Kp * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Kp * (N + 1) := by ring
  have c8 : Ksw * (vsz (.int M) + vsz (.int dl) + 1) ≤ 100 * Ksw * (N + 1) := by
    have h2 : vsz (.int M) + vsz (.int dl) + 1 ≤ 100 * (N + 1) := by
      rw [Work.Fx.vsz_int, Work.Fx.vsz_int]; omega
    calc Ksw * (vsz (.int M) + vsz (.int dl) + 1) ≤ Ksw * (100 * (N + 1)) :=
          Nat.mul_le_mul_left _ h2
      _ = 100 * Ksw * (N + 1) := by ring
  have c9 : Ksu * (isz dl + isz M) ≤ 100 * Ksu * (N + 1) := by
    have h2 : isz dl + isz M ≤ 100 * (N + 1) := by omega
    calc Ksu * (isz dl + isz M) ≤ Ksu * (100 * (N + 1)) := Nat.mul_le_mul_left _ h2
      _ = 100 * Ksu * (N + 1) := by ring
  -- the total
  set S : ℕ := 3 * Kp + Klt + Kpu + 2 * Ksu + Kad + Ksw with hS
  set BIG : ℕ := 100 * S * (N + 1) with hBIG
  have eKp : 100 * Kp * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have eKlt : 100 * Klt * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have eKpu : 100 * Kpu * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have eKsu : 100 * Ksu * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have eKad : 100 * Kad * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have eKsw : 100 * Ksw * (N + 1) ≤ BIG := by
    rw [hBIG]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have hsum : ([Kp * 7 * (Work.Fx.szl (W0.take 7) + 1),
      Kp * 2 * (Work.Fx.szl (W1.take 2) + 1),
      Klt * (isz i + isz M),
      Kpu * (vsz (.int 1) + 1),
      Ksu * (isz (1 : ℤ) + isz U),
      Kad * (isz (1 - U) + isz i),
      Kp * 7 * (Work.Fx.szl (W6.take 7) + 1),
      Ksw * (vsz (.int M) + vsz (.int dl) + 1),
      Ksu * (isz dl + isz M)] : List ℕ).sum ≤ 9 * BIG := by
    refine sum_le_length_mul _ BIG ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_trans c1 eKp
    · exact le_trans c2 eKp
    · exact le_trans c3 eKlt
    · exact le_trans c4 eKpu
    · exact le_trans c5 eKsu
    · exact le_trans c6 eKad
    · exact le_trans c7 eKp
    · exact le_trans c8 eKsw
    · exact le_trans c9 eKsu
  have hbig : 9 * BIG ≤ buArithK Kp Ksw Kpu Klt Ksu Kad * (N + 1) := by
    have h9 : 9 * BIG = 900 * S * (N + 1) := by rw [hBIG]; ring
    have hAr : buArithK Kp Ksw Kpu Klt Ksu Kad
        = 10000 * (Kp + Ksw + Kpu + Klt + Ksu + Kad + 2) := rfl
    rw [h9, hAr]
    exact Nat.mul_le_mul_right (N + 1) (by rw [hS]; omega)
  have hfinal : Kp * 7 * (Work.Fx.szl (W0.take 7) + 1)
      + (Kp * 2 * (Work.Fx.szl (W1.take 2) + 1)
      + (Klt * (isz i + isz M)
      + (Kpu * (vsz (.int 1) + 1)
      + (Ksu * (isz (1 : ℤ) + isz U)
      + (Kad * (isz (1 - U) + isz i)
      + (Kp * 7 * (Work.Fx.szl (W6.take 7) + 1)
      + (Ksw * (vsz (.int M) + vsz (.int dl) + 1) + Ksu * (isz dl + isz M))))))))
      ≤ buArithK Kp Ksw Kpu Klt Ksu Kad * (N + 1) :=
    le_trans hsum hbig
  -- the nine steps
  have s1 : Pipe main (pickProg 6) W0 W1 (Kp * 7 * (Work.Fx.szl (W0.take 7) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := W0) (k := 6) (by simp [W0, Bc, buCB])
      (v := .int M) (by
        simp only [W0, Bc, buCB, M]
        first
          | rfl
          | (simp only [List.getD_cons_succ, List.getD_cons_zero]))
  have s2 : Pipe main (pickProg 1) W1 W2 (Kp * 2 * (Work.Fx.szl (W1.take 2) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := W1) (k := 1) (by simp [W1, W0, Bc, buCB])
      (v := .int i) (by
        simp only [W1, W0, Bc, buCB]
        first
          | rfl
          | (simp only [List.getD_cons_succ, List.getD_cons_zero]))
  have s3 : Pipe main ltProg W2 W3 (Klt * (isz i + isz M)) :=
    Pipe.appendTail (main := main) (.int i :: X :: Bc)
      (Pipe.binOp (main := main) (hLt main) (a := i) (b := M) trivial)
  have s4 : Pipe main (pushProg (.int 1)) W3 W4 (Kpu * (vsz (.int 1) + 1)) :=
    Pipe.pushOnAny (T := W3) (prog := pushProg (.int 1)) (v := .int 1)
      (c := Kpu * (vsz (.int 1) + 1)) (hPush main (.int 1))
  have s5 : Pipe main subProg W4 W5 (Ksu * (isz (1 : ℤ) + isz U)) :=
    Pipe.appendTail (main := main) (.int i :: X :: Bc)
      (Pipe.binOp (main := main) (hSu main) (a := (1 : ℤ)) (b := U) trivial)
  have s6 : Pipe main addProg W5 W6 (Kad * (isz (1 - U) + isz i)) :=
    Pipe.appendTail (main := main) (X :: Bc)
      (Pipe.binOp (main := main) (hAd main) (a := (1 - U)) (b := i) trivial)
  have s7 : Pipe main (pickProg 6) W6 W7 (Kp * 7 * (Work.Fx.szl (W6.take 7) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := W6) (k := 6) (by simp [W6, Bc, buCB])
      (v := .int M) (by
        simp only [W6, Bc, buCB, M]
        first
          | rfl
          | (simp only [List.getD_cons_succ, List.getD_cons_zero]))
  have s8 : Pipe main swapProg W7 W8 (Ksw * (vsz (.int M) + vsz (.int dl) + 1)) :=
    Pipe.appendTail (main := main) (X :: Bc)
      (Pipe.swap (main := main) hSw (.int M) (.int dl))
  have s9 : Pipe main subProg W8 W9 (Ksu * (isz dl + isz M)) :=
    Pipe.appendTail (main := main) (X :: Bc)
      (Pipe.binOp (main := main) (hSu main) (a := dl) (b := M) trivial)
  -- assemble
  intro rest0
  have g1 : WordR main (pickProg 6) (fun vs => vs = W0 ++ rest0) (fun _ out => out = W1 ++ rest0)
      (fun _ => Kp * 7 * (Work.Fx.szl (W0.take 7) + 1)) := s1 rest0
  have g2 : WordR main (pickProg 1) (fun vs => vs = W1 ++ rest0) (fun _ out => out = W2 ++ rest0)
      (fun _ => Kp * 2 * (Work.Fx.szl (W1.take 2) + 1)) := s2 rest0
  have g3 : WordR main ltProg (fun vs => vs = W2 ++ rest0) (fun _ out => out = W3 ++ rest0)
      (fun _ => Klt * (isz i + isz M)) := s3 rest0
  have g4 : WordR main (pushProg (.int 1)) (fun vs => vs = W3 ++ rest0)
      (fun _ out => out = W4 ++ rest0) (fun _ => Kpu * (vsz (.int 1) + 1)) := s4 rest0
  have g5 : WordR main subProg (fun vs => vs = W4 ++ rest0) (fun _ out => out = W5 ++ rest0)
      (fun _ => Ksu * (isz (1 : ℤ) + isz U)) := s5 rest0
  have g6 : WordR main addProg (fun vs => vs = W5 ++ rest0) (fun _ out => out = W6 ++ rest0)
      (fun _ => Kad * (isz (1 - U) + isz i)) := s6 rest0
  have g7 : WordR main (pickProg 6) (fun vs => vs = W6 ++ rest0) (fun _ out => out = W7 ++ rest0)
      (fun _ => Kp * 7 * (Work.Fx.szl (W6.take 7) + 1)) := s7 rest0
  have g8 : WordR main swapProg (fun vs => vs = W7 ++ rest0) (fun _ out => out = W8 ++ rest0)
      (fun _ => Ksw * (vsz (.int M) + vsz (.int dl) + 1)) := s8 rest0
  have g9 : WordR main subProg (fun vs => vs = W8 ++ rest0) (fun _ out => out = W9 ++ rest0)
      (fun _ => Ksu * (isz dl + isz M)) := s9 rest0
  have gtot := buCol_comp g1 (buCol_comp g2 (buCol_comp g3 (buCol_comp g4 (buCol_comp g5
    (buCol_comp g6 (buCol_comp g7 (buCol_comp g8 g9)))))))
  refine Work.Kernel.WordR_conseq gtot (fun vs hv => hv) ?_ (fun vs _ => hfinal)
  intro vs out hv hout
  rw [hout]
  dsimp only [W9]
  first
    | rw [hval]
    | (rw [hval]; rfl)

end Work.Resample
