import Mathlib
import Submission.Work.Resample.auKit2

set_option autoImplicit false
set_option maxHeartbeats 100000000

namespace Work.Resample
open HvdH Work.Fx

/-- One round of the Horner loop. -/
theorem auRoundWordP (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (body : HvdH.Cmd) (KS : ℕ),
      ∀ (main : HvdH.Cmd) (p : ℕ) (cnt Z E E2 Q : ℤ) (rest : List Val),
        (0 < cnt) → (0 < E) →
        (cnt.natAbs ≤ 2 ^ (p + 11)) → (Z.natAbs ≤ 2 ^ (4 * p + 110)) →
        (Q.natAbs ≤ 2 ^ (5 * p + 130)) → (E.natAbs ≤ 2 ^ (3 * p + 101)) →
        (E2.natAbs ≤ 2 ^ (3 * p + 104)) →
        WordR main body
          (fun vs => vs = [.int cnt, .int Q, .int Z, .int E, .int E2] ++ rest)
          (fun _ out => out = [.int (if (0 : ℤ) < cnt - 1 then 1 else 0), .int (cnt - 1),
            .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E, .int E2] ++ rest)
          (fun _ => 100 * auSB p KS) := by
  obtain ⟨mulP, Kmul, hMul⟩ := hi.mulS
  obtain ⟨negP, Kne, hNeg⟩ := hi.neg
  obtain ⟨tdivP, Ktdiv, hTdiv⟩ := hi.tdiv
  obtain ⟨addP, Kadd, hAdd⟩ := hi.add
  obtain ⟨subP, Ksub, hSub⟩ := hi.sub
  obtain ⟨ltP, Klt, hLt⟩ := hi.lt
  obtain ⟨pickP, Kpick, hPick⟩ := hk.pick
  obtain ⟨dropP, Kdrop, hDrop⟩ := hk.drop
  obtain ⟨swapP, Kswap, hSwap⟩ := hk.swap
  obtain ⟨rollP, Kroll, hRoll⟩ := hk.roll
  obtain ⟨pushP, Kpush, hPush⟩ := hk.pushVal
  set KS : ℕ := Kmul + Kne + Ktdiv + Kadd + Ksub + Klt + Kpick + Kdrop + Kswap + Kroll + Kpush + 1
    with hKS
  have hKmul : Kmul ≤ KS := by omega
  have hKne : Kne ≤ KS := by omega
  have hKtdiv : Ktdiv ≤ KS := by omega
  have hKadd : Kadd ≤ KS := by omega
  have hKsub : Ksub ≤ KS := by omega
  have hKlt : Klt ≤ KS := by omega
  have hKpick : Kpick ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  have hKswap : Kswap ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKpush : Kpush ≤ KS := by omega
  let body : Cmd :=
    .seq (.seq (pickP 0) (.seq (pushP (Val.int 1)) (.seq swapP subP))) (.seq (.seq (pickP 2) (.seq (pickP 4) (.seq mulP negP))) (.seq (.seq (pickP 5) (.seq swapP tdivP)) (.seq (.seq (pickP 2) (.seq swapP tdivP)) (.seq (.seq (pickP 5) addP) (.seq (.seq (rollP 3) dropP) (.seq (.seq (rollP 2) dropP) (.seq swapP (.seq (pickP 0) (.seq (pushP (Val.int 0)) ltP)))))))))
  refine ⟨body, KS, ?_⟩
  intro main p cnt Z E E2 Q rest hcnt hE hcntsz hZsz hQsz hEsz hE2sz
  -- sharp size bounds of the values occurring on the way
  have hiz_cnt : isz cnt ≤ p + 14 := by
    have h1 : cnt.natAbs.size ≤ p + 12 :=
      Nat.size_le.mpr (lt_of_le_of_lt hcntsz
        (Nat.pow_lt_pow_right one_lt_two (by omega : p + 11 < p + 12)))
    rw [isz]; omega
  have hiz_Z : isz Z ≤ 4 * p + 113 := by
    have h1 : Z.natAbs.size ≤ 4 * p + 111 :=
      Nat.size_le.mpr (lt_of_le_of_lt hZsz
        (Nat.pow_lt_pow_right one_lt_two (by omega : 4 * p + 110 < 4 * p + 111)))
    rw [isz]; omega
  have hiz_Q : isz Q ≤ 5 * p + 133 := by
    have h1 : Q.natAbs.size ≤ 5 * p + 131 :=
      Nat.size_le.mpr (lt_of_le_of_lt hQsz
        (Nat.pow_lt_pow_right one_lt_two (by omega : 5 * p + 130 < 5 * p + 131)))
    rw [isz]; omega
  have hiz_E : isz E ≤ 3 * p + 104 := by
    have h1 : E.natAbs.size ≤ 3 * p + 102 :=
      Nat.size_le.mpr (lt_of_le_of_lt hEsz
        (Nat.pow_lt_pow_right one_lt_two (by omega : 3 * p + 101 < 3 * p + 102)))
    rw [isz]; omega
  have hiz_E2 : isz E2 ≤ 3 * p + 107 := by
    have h1 : E2.natAbs.size ≤ 3 * p + 105 :=
      Nat.size_le.mpr (lt_of_le_of_lt hE2sz
        (Nat.pow_lt_pow_right one_lt_two (by omega : 3 * p + 104 < 3 * p + 105)))
    rw [isz]; omega
  have hiz_c1 : isz (cnt - 1) ≤ p + 15 := by
    have h := isz_sub_le cnt 1
    have h1 : isz (1 : ℤ) ≤ p + 14 := by
      have h0 : isz (1 : ℤ) ≤ 5 := by decide
      omega
    have hm : max (isz cnt) (isz (1 : ℤ)) ≤ p + 14 := max_le hiz_cnt h1
    omega
  have hiz_T : isz (Z * Q) ≤ 9 * p + 246 := by
    have h := isz_mul_le Z Q
    omega
  have hiz_nT : isz (-(Z * Q)) ≤ 9 * p + 246 := by rw [isz_neg]; exact hiz_T
  have hiz_U : isz (Int.tdiv (-(Z * Q)) E) ≤ 9 * p + 246 :=
    le_trans (isz_tdiv_le (-(Z * Q)) E) hiz_nT
  have hiz_V : isz (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt) ≤ 9 * p + 246 :=
    le_trans (isz_tdiv_le (Int.tdiv (-(Z * Q)) E) cnt) hiz_U
  have hiz_A : isz (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt) ≤ 9 * p + 247 := by
    have h := isz_add_le E (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt)
    have hm : max (isz E) (isz (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt)) ≤ 9 * p + 246 :=
      max_le (by omega) (by omega)
    omega
  -- `≤ auSZ p` versions
  have hsz_cnt : isz cnt ≤ auSZ p := le_trans hiz_cnt (by simp only [auSZ]; omega)
  have hsz_Z : isz Z ≤ auSZ p := le_trans hiz_Z (by simp only [auSZ]; omega)
  have hsz_Q : isz Q ≤ auSZ p := le_trans hiz_Q (by simp only [auSZ]; omega)
  have hsz_E : isz E ≤ auSZ p := le_trans hiz_E (by simp only [auSZ]; omega)
  have hsz_E2 : isz E2 ≤ auSZ p := le_trans hiz_E2 (by simp only [auSZ]; omega)
  have hsz_c1 : isz (cnt - 1) ≤ auSZ p := le_trans hiz_c1 (by simp only [auSZ]; omega)
  have hsz_T : isz (Z * Q) ≤ auSZ p := le_trans hiz_T (by simp only [auSZ]; omega)
  have hsz_nT : isz (-(Z * Q)) ≤ auSZ p := by rw [isz_neg]; exact hsz_T
  have hsz_U : isz (Int.tdiv (-(Z * Q)) E) ≤ auSZ p :=
    le_trans (isz_tdiv_le (-(Z * Q)) E) hsz_nT
  have hsz_V : isz (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt) ≤ auSZ p :=
    le_trans (isz_tdiv_le (Int.tdiv (-(Z * Q)) E) cnt) hsz_U
  have hsz_A : isz (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt) ≤ auSZ p :=
    le_trans hiz_A (by simp only [auSZ]; omega)
  have hsz_one : isz (1 : ℤ) ≤ auSZ p := le_trans (by decide : isz (1 : ℤ) ≤ 5)
    (by simp only [auSZ]; omega)
  have hsz_zero : isz (0 : ℤ) ≤ auSZ p := le_trans (by decide : isz (0 : ℤ) ≤ 5)
    (by simp only [auSZ]; omega)
  -- `vsz` versions
  have hvsz_cnt : vsz (Val.int cnt) ≤ auSZ p := by rw [vsz_int]; exact hsz_cnt
  have hvsz_Z : vsz (Val.int Z) ≤ auSZ p := by rw [vsz_int]; exact hsz_Z
  have hvsz_Q : vsz (Val.int Q) ≤ auSZ p := by rw [vsz_int]; exact hsz_Q
  have hvsz_E : vsz (Val.int E) ≤ auSZ p := by rw [vsz_int]; exact hsz_E
  have hvsz_E2 : vsz (Val.int E2) ≤ auSZ p := by rw [vsz_int]; exact hsz_E2
  have hvsz_c1 : vsz (Val.int (cnt - 1)) ≤ auSZ p := by rw [vsz_int]; exact hsz_c1
  have hvsz_nT : vsz (Val.int (-(Z * Q))) ≤ auSZ p := by rw [vsz_int]; exact hsz_nT
  have hvsz_U : vsz (Val.int (Int.tdiv (-(Z * Q)) E)) ≤ auSZ p := by rw [vsz_int]; exact hsz_U
  have hvsz_V : vsz (Val.int (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt)) ≤ auSZ p := by
    rw [vsz_int]; exact hsz_V
  have hvsz_A : vsz (Val.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt)) ≤ auSZ p := by
    rw [vsz_int]; exact hsz_A
  have hvsz_one : vsz (Val.int (1 : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_one
  have hvsz_zero : vsz (Val.int (0 : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_zero
  have hone : 1 ≤ auSZ p := by simp only [auSZ]; omega
  -- the chain
  have s1 := Pipe.le (Pipe.pickAt main hPick (A := [.int cnt, .int Q, .int Z, .int E, .int E2])
      (k := 0) (by simp) (v := .int cnt) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s2 := Pipe.le (Pipe.pushOnAny (T := [.int cnt, .int cnt, .int Q, .int Z, .int E, .int E2])
      (hPush main (Val.int 1))) (au_le_one hKpush hvsz_one)
  have s3 := Pipe.le (Pipe.appendTail [.int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.swap main hSwap (.int 1) (.int cnt)))
    (au_le_three hKswap hvsz_one hvsz_cnt hone)
  have s4 := Pipe.le (Pipe.appendTail [.int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.binOp (hSub main) (a := cnt) (b := (1 : ℤ)) trivial))
    (au_le_two hKsub hsz_cnt hsz_one)
  have s5 := Pipe.le (Pipe.pickAt main hPick (A := [.int (cnt - 1), .int cnt, .int Q, .int Z,
      .int E, .int E2]) (k := 2) (by simp) (v := .int Q) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s6 := Pipe.le (Pipe.pickAt main hPick (A := [.int Q, .int (cnt - 1), .int cnt, .int Q,
      .int Z, .int E, .int E2]) (k := 4) (by simp) (v := .int Z) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s7 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.binOp (hMul main) (a := Z) (b := Q) trivial))
    (au_le_mul hKmul hsz_Z hsz_Q)
  have s8 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.unOp (hNeg main) (a := Z * Q) trivial))
    (au_le_mone hKne hsz_T)
  have s9 := Pipe.le (Pipe.pickAt main hPick (A := [.int (-(Z * Q)), .int (cnt - 1), .int cnt,
      .int Q, .int Z, .int E, .int E2]) (k := 5) (by simp) (v := .int E) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s10 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.swap main hSwap (.int E) (.int (-(Z * Q)))))
    (au_le_three hKswap hvsz_E hvsz_nT hone)
  have s11 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.binOp (hTdiv main) (a := -(Z * Q)) (b := E) (show E ≠ 0 by omega)))
    (au_le_mul hKtdiv hsz_nT hsz_E)
  have s12 := Pipe.le (Pipe.pickAt main hPick (A := [.int (Int.tdiv (-(Z * Q)) E), .int (cnt - 1),
      .int cnt, .int Q, .int Z, .int E, .int E2]) (k := 2) (by simp) (v := .int cnt) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s13 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.swap main hSwap (.int cnt) (.int (Int.tdiv (-(Z * Q)) E))))
    (au_le_three hKswap hvsz_cnt hvsz_U hone)
  have s14 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.binOp (hTdiv main) (a := Int.tdiv (-(Z * Q)) E) (b := cnt) (show cnt ≠ 0 by omega)))
    (au_le_mul hKtdiv hsz_U hsz_cnt)
  have s15 := Pipe.le (Pipe.pickAt main hPick
      (A := [.int (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q,
        .int Z, .int E, .int E2]) (k := 5) (by simp) (v := .int E) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s16 := Pipe.le (Pipe.appendTail [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      (Pipe.binOp (hAdd main) (a := E) (b := Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt) trivial))
    (au_le_two hKadd hsz_E hsz_V)
  have s17 : Pipe main (rollP 3)
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q, .int Z,
        .int E, .int E2]
      [.int Q, .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Z,
        .int E, .int E2] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll (A := [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt),
      .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]) (k := 3) (by simp)) (by simp))
    (au_le_roll hKroll (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s18 := Pipe.le (Pipe.appendTail [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt),
      .int (cnt - 1), .int cnt, .int Z, .int E, .int E2] (Pipe.drop main hDrop (.int Q)))
    (au_le_one hKdrop hvsz_Q)
  have s19 : Pipe main (rollP 2)
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Z,
        .int E, .int E2]
      [.int cnt, .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int Z,
        .int E, .int E2] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll (A := [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt),
      .int (cnt - 1), .int cnt, .int Z, .int E, .int E2]) (k := 2) (by simp)) (by simp))
    (au_le_roll hKroll (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s20 := Pipe.le (Pipe.appendTail [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt),
      .int (cnt - 1), .int Z, .int E, .int E2] (Pipe.drop main hDrop (.int cnt)))
    (au_le_one hKdrop hvsz_cnt)
  have s21 := Pipe.le (Pipe.appendTail [.int Z, .int E, .int E2]
      (Pipe.swap main hSwap (.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt)) (.int (cnt - 1))))
    (au_le_three hKswap hvsz_A hvsz_c1 hone)
  have s22 := Pipe.le (Pipe.pickAt main hPick
      (A := [.int (cnt - 1), .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E,
        .int E2]) (k := 0) (by simp) (v := .int (cnt - 1)) (rfl))
    (au_le_roll hKpick (by simp) (by simp)
      (by intro v hv
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp only [vsz_int] <;> assumption))
  have s23 := Pipe.le (Pipe.pushOnAny (T := [.int (cnt - 1), .int (cnt - 1),
      .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E, .int E2])
      (hPush main (Val.int 0))) (au_le_one hKpush hvsz_zero)
  have s24 := Pipe.le (Pipe.appendTail [.int (cnt - 1),
      .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E, .int E2]
      (Pipe.binOp (hLt main) (a := (0 : ℤ)) (b := cnt - 1) trivial))
    (au_le_two hKlt hsz_zero hsz_c1)

  have g1 : Pipe main (.seq (pickP 0) (.seq (pushP (Val.int 1)) (.seq swapP subP)))
      [.int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2] (4 * auSB p KS) :=
    Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 s4))) (by omega)
  have g2 : Pipe main (.seq (pickP 2) (.seq (pickP 4) (.seq mulP negP)))
      [.int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (-(Z * Q)), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2] (4 * auSB p KS) :=
    Pipe.le (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 s8))) (by omega)
  have g3 : Pipe main (.seq (pickP 5) (.seq swapP tdivP))
      [.int (-(Z * Q)), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (Int.tdiv (-(Z * Q)) E), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2] (3 * auSB p KS) :=
    Pipe.le (Pipe.comp s9 (Pipe.comp s10 s11)) (by omega)
  have g4 : Pipe main (.seq (pickP 2) (.seq swapP tdivP))
      [.int (Int.tdiv (-(Z * Q)) E), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2] (3 * auSB p KS) :=
    Pipe.le (Pipe.comp s12 (Pipe.comp s13 s14)) (by omega)
  have g5 : Pipe main (.seq (pickP 5) addP)
      [.int (Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2] (2 * auSB p KS) :=
    Pipe.le (Pipe.comp s15 s16) (by omega)
  have g6 : Pipe main (.seq (rollP 3) dropP)
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Z, .int E, .int E2] (2 * auSB p KS) :=
    Pipe.le (Pipe.comp s17 s18) (by omega)
  have g7 : Pipe main (.seq (rollP 2) dropP)
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int cnt, .int Z, .int E, .int E2]
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int Z, .int E, .int E2] (2 * auSB p KS) :=
    Pipe.le (Pipe.comp s19 s20) (by omega)
  have g8 : Pipe main (.seq swapP (.seq (pickP 0) (.seq (pushP (Val.int 0)) ltP)))
      [.int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int (cnt - 1), .int Z, .int E, .int E2]
      [.int (if (0 : ℤ) < cnt - 1 then 1 else 0), .int (cnt - 1), .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E, .int E2] (4 * auSB p KS) :=
    Pipe.le (Pipe.comp s21 (Pipe.comp s22 (Pipe.comp s23 s24))) (by omega)
  have hPipe : Pipe main body
      [.int cnt, .int Q, .int Z, .int E, .int E2]
      [.int (if (0 : ℤ) < cnt - 1 then 1 else 0), .int (cnt - 1), .int (E + Int.tdiv (Int.tdiv (-(Z * Q)) E) cnt), .int Z, .int E, .int E2]
      (24 * auSB p KS) :=
    Pipe.le (Pipe.comp g1 (Pipe.comp g2 (Pipe.comp g3 (Pipe.comp g4 (Pipe.comp g5 (Pipe.comp g6 (Pipe.comp g7 g8))))))) (by omega)
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hPipe rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn (Nat.mul_le_mul_right (auSB p KS) (by norm_num)), hstk, hoth⟩


end Work.Resample
