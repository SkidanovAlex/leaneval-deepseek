import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buZbKit
import Submission.Work.Resample.buWdKit

/-!
# The `buZb` word (the diagonal weight exponent of the one-dimensional `B̃` resampling)

`buZbWord` builds the word computing `buZb p α s t ℓ` from the canonical block
`[Val.int ℓ] ++ buCB p α s t = [ℓ, p, α, s, t, m, n, π]`, as a chain of `KernelLib` / `IntLib`
primitives.  All the values met on the way are the ones defined in `Submission.Work.Resample.buZbKit`
(`buA`, `buAA`, `buAAs`, `buS2`, `buQ`, `buQS`, `buBeta`, `buBB`, `buAl2`, `buAlBB`, `buPAlBB`,
`buSS`, `buZb`), and every step is a `Work.Resample.Pipe` on the full window, bounded by
`KS * (buSZ p + 8) ^ 2`; the 31 steps are absorbed into a single `K * (p+1)^K` by `buStepCost`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-- Transporting a `Pipe` along an equality of its *input* window. -/
private theorem Pipe.rwA {main prog : Cmd} {A A' B : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hA : A = A') : Pipe main prog A' B c := hA ▸ h

/-- The word computing `buZb p α s t ℓ` from the block `[ℓ] ++ buCB p α s t`. -/
theorem buZbWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s)
      (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)),
      Work.Resample.Pipe main prog
        ([HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t)
        ([HvdH.Val.int (Work.Resample.buZb p α s t ℓ), HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t)
        (K * (p + 1) ^ K) := by
  obtain ⟨cPick, KPick, hPick⟩ := KL.pick
  obtain ⟨cSwap, KSwap, hSwap⟩ := KL.swap
  obtain ⟨cDup, KDup, hDup⟩ := KL.dup
  obtain ⟨cMul, KMul, hMul⟩ := IL.mulS
  obtain ⟨cAdd, KAdd, hAdd⟩ := IL.add
  obtain ⟨cSub, KSub, hSub⟩ := IL.sub
  obtain ⟨cFdiv, KFdiv, hFdiv⟩ := IL.fdiv
  obtain ⟨cTdiv, KTdiv, hTdiv⟩ := IL.tdiv
  let KS : ℕ := 200 * (KPick + KSwap + KDup + KMul + KAdd + KSub + KFdiv + KTdiv + 1)
  let prog : Cmd := .seq (cPick 4) (.seq (cPick 1) (.seq (cSwap) (.seq (cMul) (.seq (cDup) (.seq (cPick 1) (.seq (cAdd) (.seq (cPick 5) (.seq (cAdd) (.seq (cPick 5) (.seq (cDup) (.seq (cAdd) (.seq (cSwap) (.seq (cFdiv) (.seq (cPick 5) (.seq (cMul) (.seq (cSwap) (.seq (cSub) (.seq (cDup) (.seq (cMul) (.seq (cPick 3) (.seq (cDup) (.seq (cMul) (.seq (cMul) (.seq (cPick 8) (.seq (cMul) (.seq (cPick 4) (.seq (cDup) (.seq (cMul) (.seq (cSwap) ((cTdiv)))))))))))))))))))))))))))))))
  refine ⟨prog, 256 * KS + 256, ?_⟩
  intro main p α s t hs hst hα hp htp hαp ℓ hℓ hℓs
  have hsp : s < 2 ^ p := lt_trans hst htp
  have hs0 : 0 < s := by omega
  have hαlt : α < 2 ^ p := by
    have h1 : α < p := by nlinarith
    exact lt_of_lt_of_le h1 (le_of_lt (Nat.lt_two_pow_self))
  have hiszℓ : isz ℓ ≤ buSZ p := isz_le_buSZ_of_nonneg_lt hℓ hℓs hsp
  have hiszp : isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ p
  have hiszα : isz ((α : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hαlt
  have hiszs : isz ((s : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hsp
  have hiszt : isz ((t : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt htp
  have hiszM : isz (((egM p α : ℕ) : ℤ)) ≤ buSZ p := isz_egM_le p α
  have hiszN : isz (((egN p α s t : ℕ) : ℤ)) ≤ buSZ p := isz_egN_le p α s t hs0 hsp (by omega)
  have hiszP : isz (auPi p) ≤ buSZ p := isz_auPi_le_buSZ p
  have hiszA : isz (buA t ℓ) ≤ buSZ p := isz_buA_le p s t ℓ hℓ hℓs hsp htp hp
  have hiszAA : isz (buAA t ℓ) ≤ buSZ p := isz_buAA_le p s t ℓ hℓ hℓs hsp htp hp
  have hiszAAs : isz (buAAs s t ℓ) ≤ buSZ p := isz_buAAs_le p s t ℓ hℓ hℓs hsp htp hp
  have hiszS2 : isz (buS2 s) ≤ buSZ p := isz_buS2_le p s hsp hp
  have hiszQ : isz (buQ s t ℓ) ≤ buSZ p := isz_buQ_le p s t ℓ hℓ hℓs hs0 hsp htp hp
  have hiszQS : isz (buQS s t ℓ) ≤ buSZ p := isz_buQS_le p s t ℓ hℓ hℓs hs0 hsp htp hp
  have hiszBeta : isz (buBeta s t ℓ) ≤ buSZ p := isz_buBeta_le p s t hs0 hsp hp ℓ
  have hiszBB : isz (buBB s t ℓ) ≤ buSZ p := isz_buBB_le p s t ℓ hs0 hsp hp
  have hiszAl2 : isz (buAl2 α) ≤ buSZ p := isz_buAl2_le p α hαp hp
  have hiszAlBB : isz (buAlBB α s t ℓ) ≤ buSZ p := isz_buAlBB_le p α s t ℓ hαp hs0 hsp hp
  have hiszPAlBB : isz (buPAlBB p α s t ℓ) ≤ buSZ p := isz_buPAlBB_le p α s t ℓ hαp hs0 hsp hp
  have hiszSS : isz (buSS s) ≤ buSZ p := isz_buSS_le p s hsp hp
  have hiszAr : isz ((t : ℤ) * ℓ) ≤ buSZ p := by simpa only [buA] using hiszA
  have hiszAAr : isz ((t : ℤ) * ℓ + (t : ℤ) * ℓ) ≤ buSZ p := by
    simpa only [buAA, buA] using hiszAA
  have hiszAAsr : isz ((s : ℤ) + ((t : ℤ) * ℓ + (t : ℤ) * ℓ)) ≤ buSZ p := by
    simpa only [buAAs, buAA, buA] using hiszAAs
  have hiszS2r : isz ((s : ℤ) + (s : ℤ)) ≤ buSZ p := by simpa only [buS2] using hiszS2
  have hiszQr : isz (Int.fdiv ((s : ℤ) + ((t : ℤ) * ℓ + (t : ℤ) * ℓ))
      ((s : ℤ) + (s : ℤ))) ≤ buSZ p := by
    simpa only [buQ, buAAs, buAA, buA, buS2] using hiszQ
  have hiszQSr : isz ((s : ℤ) * Int.fdiv ((s : ℤ) + ((t : ℤ) * ℓ + (t : ℤ) * ℓ))
      ((s : ℤ) + (s : ℤ))) ≤ buSZ p := by
    simpa only [buQS, buQ, buAAs, buAA, buA, buS2] using hiszQS
  have hiszBBr : isz (buBeta s t ℓ * buBeta s t ℓ) ≤ buSZ p := by
    simpa only [buBB] using hiszBB
  have hiszAl2r : isz ((α : ℤ) * (α : ℤ)) ≤ buSZ p := by simpa only [buAl2] using hiszAl2
  have hiszAlBBr : isz (((α : ℤ) * (α : ℤ)) * (buBeta s t ℓ * buBeta s t ℓ)) ≤ buSZ p := by
    simpa only [buAlBB, buAl2, buBB] using hiszAlBB
  have hiszPAlBBr : isz (auPi p * (((α : ℤ) * (α : ℤ)) * (buBeta s t ℓ * buBeta s t ℓ)))
      ≤ buSZ p := by
    simpa only [buPAlBB, buAlBB, buAl2, buBB] using hiszPAlBB
  have hiszSSr : isz ((s : ℤ) * (s : ℤ)) ≤ buSZ p := by simpa only [buSS] using hiszSS
  let BK : List Val := [Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]
  let W0 : List Val := BK
  let W1 : List Val := [Val.int (t : ℤ)] ++ BK
  let W2 : List Val := [Val.int ℓ, Val.int (t : ℤ)] ++ BK
  let W3 : List Val := [Val.int (t : ℤ), Val.int ℓ] ++ BK
  let W4 : List Val := [Val.int (buA t ℓ)] ++ BK
  let W5 : List Val := [Val.int (buA t ℓ), Val.int (buA t ℓ)] ++ BK
  let W6 : List Val := [Val.int (buA t ℓ), Val.int (buA t ℓ), Val.int (buA t ℓ)] ++ BK
  let W7 : List Val := [Val.int (buAA t ℓ), Val.int (buA t ℓ)] ++ BK
  let W8 : List Val := [Val.int (s : ℤ), Val.int (buAA t ℓ), Val.int (buA t ℓ)] ++ BK
  let W9 : List Val := [Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W10 : List Val := [Val.int (s : ℤ), Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W11 : List Val := [Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W12 : List Val := [Val.int (buS2 s), Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W13 : List Val := [Val.int (buAAs s t ℓ), Val.int (buS2 s), Val.int (buA t ℓ)] ++ BK
  let W14 : List Val := [Val.int (buQ s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W15 : List Val := [Val.int (s : ℤ), Val.int (buQ s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W16 : List Val := [Val.int (buQS s t ℓ), Val.int (buA t ℓ)] ++ BK
  let W17 : List Val := [Val.int (buA t ℓ), Val.int (buQS s t ℓ)] ++ BK
  let W18 : List Val := [Val.int (buBeta s t ℓ)] ++ BK
  let W19 : List Val := [Val.int (buBeta s t ℓ), Val.int (buBeta s t ℓ)] ++ BK
  let W20 : List Val := [Val.int (buBB s t ℓ)] ++ BK
  let W21 : List Val := [Val.int (α : ℤ), Val.int (buBB s t ℓ)] ++ BK
  let W22 : List Val := [Val.int (α : ℤ), Val.int (α : ℤ), Val.int (buBB s t ℓ)] ++ BK
  let W23 : List Val := [Val.int (buAl2 α), Val.int (buBB s t ℓ)] ++ BK
  let W24 : List Val := [Val.int (buAlBB α s t ℓ)] ++ BK
  let W25 : List Val := [Val.int (auPi p), Val.int (buAlBB α s t ℓ)] ++ BK
  let W26 : List Val := [Val.int (buPAlBB p α s t ℓ)] ++ BK
  let W27 : List Val := [Val.int (s : ℤ), Val.int (buPAlBB p α s t ℓ)] ++ BK
  let W28 : List Val := [Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buPAlBB p α s t ℓ)] ++ BK
  let W29 : List Val := [Val.int (buSS s), Val.int (buPAlBB p α s t ℓ)] ++ BK
  let W30 : List Val := [Val.int (buPAlBB p α s t ℓ), Val.int (buSS s)] ++ BK
  let W31 : List Val := [Val.int (buZb p α s t ℓ)] ++ BK
  have e1 : Pipe main (cPick 4) W0 W1 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 4 < W0.length := by
      simp only [W0, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W0.take (4 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W0, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W0) (k := 4) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e2 : Pipe main (cPick 1) W1 W2 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 1 < W1.length := by
      simp only [W1, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W1.take (1 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W1, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W1) (k := 1) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e3 : Pipe main cSwap W2 W3 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.swap main hSwap (Val.int ℓ) (Val.int (t : ℤ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact swapCost (hBT := by omega) (ha := by simp only [vsz_int]; omega)
        (hb := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e4 : Pipe main cMul W3 W4 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hMul main) (a := (t : ℤ)) (b := ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W4, buA, BK, List.cons_append, List.nil_append]

  have e5 : Pipe main cDup W4 W5 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.dup main hDup (Val.int (buA t ℓ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact dupCost (hBT := by omega) (ha := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e6 : Pipe main (cPick 1) W5 W6 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 1 < W5.length := by
      simp only [W5, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W5.take (1 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W5, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W5) (k := 1) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e7 : Pipe main cAdd W6 W7 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buA t ℓ)] ++ BK) (Pipe.binOp (hAdd main) (a := buA t ℓ) (b := buA t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binAddCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W7, buAA, BK, List.cons_append, List.nil_append]

  have e8 : Pipe main (cPick 5) W7 W8 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 5 < W7.length := by
      simp only [W7, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W7.take (5 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W7, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W7) (k := 5) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e9 : Pipe main cAdd W8 W9 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buA t ℓ)] ++ BK) (Pipe.binOp (hAdd main) (a := (s : ℤ)) (b := buAA t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binAddCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W9, buAAs, BK, List.cons_append, List.nil_append]

  have e10 : Pipe main (cPick 5) W9 W10 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 5 < W9.length := by
      simp only [W9, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W9.take (5 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W9, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W9) (k := 5) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e11 : Pipe main cDup W10 W11 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK) (Pipe.dup main hDup (Val.int (s : ℤ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact dupCost (hBT := by omega) (ha := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e12 : Pipe main cAdd W11 W12 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buAAs s t ℓ), Val.int (buA t ℓ)] ++ BK) (Pipe.binOp (hAdd main) (a := (s : ℤ)) (b := (s : ℤ)) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binAddCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W12, buS2, BK, List.cons_append, List.nil_append]

  have e13 : Pipe main cSwap W12 W13 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buA t ℓ)] ++ BK) (Pipe.swap main hSwap (Val.int (buS2 s)) (Val.int (buAAs s t ℓ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact swapCost (hBT := by omega) (ha := by simp only [vsz_int]; omega)
        (hb := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e14 : Pipe main cFdiv W13 W14 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buA t ℓ)] ++ BK) (Pipe.binOp (hFdiv main) (a := buAAs s t ℓ) (b := buS2 s) (hab := by simp only [buS2]; omega))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W14, buQ, BK, List.cons_append, List.nil_append]

  have e15 : Pipe main (cPick 5) W14 W15 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 5 < W14.length := by
      simp only [W14, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W14.take (5 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W14, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W14) (k := 5) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e16 : Pipe main cMul W15 W16 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buA t ℓ)] ++ BK) (Pipe.binOp (hMul main) (a := (s : ℤ)) (b := buQ s t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W16, buQS, BK, List.cons_append, List.nil_append]

  have e17 : Pipe main cSwap W16 W17 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.swap main hSwap (Val.int (buQS s t ℓ)) (Val.int (buA t ℓ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact swapCost (hBT := by omega) (ha := by simp only [vsz_int]; omega)
        (hb := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e18 : Pipe main cSub W17 W18 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hSub main) (a := buA t ℓ) (b := buQS s t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binAddCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W18, BK, buBeta_eq_buQS s t hs0 ℓ, List.cons_append, List.nil_append]

  have e19 : Pipe main cDup W18 W19 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.dup main hDup (Val.int (buBeta s t ℓ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact dupCost (hBT := by omega) (ha := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e20 : Pipe main cMul W19 W20 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hMul main) (a := buBeta s t ℓ) (b := buBeta s t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W20, buBB, BK, List.cons_append, List.nil_append]

  have e21 : Pipe main (cPick 3) W20 W21 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 3 < W20.length := by
      simp only [W20, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W20.take (3 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W20, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W20) (k := 3) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e22 : Pipe main cDup W21 W22 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buBB s t ℓ)] ++ BK) (Pipe.dup main hDup (Val.int (α : ℤ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact dupCost (hBT := by omega) (ha := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e23 : Pipe main cMul W22 W23 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buBB s t ℓ)] ++ BK) (Pipe.binOp (hMul main) (a := (α : ℤ)) (b := (α : ℤ)) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W23, buAl2, BK, List.cons_append, List.nil_append]

  have e24 : Pipe main cMul W23 W24 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hMul main) (a := buAl2 α) (b := buBB s t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W24, buAlBB, BK, List.cons_append, List.nil_append]

  have e25 : Pipe main (cPick 8) W24 W25 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 8 < W24.length := by
      simp only [W24, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W24.take (8 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W24, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W24) (k := 8) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e26 : Pipe main cMul W25 W26 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hMul main) (a := auPi p) (b := buAlBB α s t ℓ) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W26, buPAlBB, BK, List.cons_append, List.nil_append]

  have e27 : Pipe main (cPick 4) W26 W27 (KS * (buSZ p + 8) ^ 2) := by
    have hlt : 4 < W26.length := by
      simp only [W26, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    have hsz : szl (W26.take (4 + 1)) + 1 ≤ 13 * (buSZ p + 8) := by
      simp only [W26, BK, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil, szl_cons, szl_nil, vsz_int, buCB, buA, buAA, buAAs, buS2, buQ, buQS, buBB, buAl2, buAlBB, buPAlBB, buSS]
      omega
    refine Pipe.rw (Pipe.le (Pipe.pick main hPick (A := W26) (k := 4) hlt) ?_) ?_
    · exact pickCost (hBT := by omega) (hk := by norm_num) (hsz := hsz) (hC := by simp only [KS]; omega)
    · rfl

  have e28 : Pipe main cDup W27 W28 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buPAlBB p α s t ℓ)] ++ BK) (Pipe.dup main hDup (Val.int (s : ℤ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact dupCost (hBT := by omega) (ha := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e29 : Pipe main cMul W28 W29 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int (buPAlBB p α s t ℓ)] ++ BK) (Pipe.binOp (hMul main) (a := (s : ℤ)) (b := (s : ℤ)) (hab := trivial))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W29, buSS, BK, List.cons_append, List.nil_append]

  have e30 : Pipe main cSwap W29 W30 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.swap main hSwap (Val.int (buSS s)) (Val.int (buPAlBB p α s t ℓ)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact swapCost (hBT := by omega) (ha := by simp only [vsz_int]; omega)
        (hb := by simp only [vsz_int]; omega) (hC := by simp only [KS]; omega)
    · rfl

  have e31 : Pipe main cTdiv W30 W31 (KS * (buSZ p + 8) ^ 2) := by
    have h := Pipe.appendTail ([Val.int ℓ, Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (((egM p α : ℕ) : ℤ)), Val.int (((egN p α s t : ℕ) : ℤ)), Val.int (auPi p)]) (Pipe.binOp (hTdiv main) (a := buPAlBB p α s t ℓ) (b := buSS s) (hab := by simp only [buSS]; exact mul_ne_zero (by omega) (by omega)))
    refine Pipe.rw (Pipe.le h ?_) ?_
    · exact binMulCost (hBT := by omega) (ha := by omega) (hb := by omega)
        (hC := by simp only [KS]; omega)
    · simp only [W31, BK, buZb_eq_tdiv p α s t ℓ, List.cons_append, List.nil_append]

  have hmain := Pipe.comp e1 (Pipe.comp e2 (Pipe.comp e3 (Pipe.comp e4 (Pipe.comp e5 (Pipe.comp e6 (Pipe.comp e7 (Pipe.comp e8 (Pipe.comp e9 (Pipe.comp e10 (Pipe.comp e11 (Pipe.comp e12 (Pipe.comp e13 (Pipe.comp e14 (Pipe.comp e15 (Pipe.comp e16 (Pipe.comp e17 (Pipe.comp e18 (Pipe.comp e19 (Pipe.comp e20 (Pipe.comp e21 (Pipe.comp e22 (Pipe.comp e23 (Pipe.comp e24 (Pipe.comp e25 (Pipe.comp e26 (Pipe.comp e27 (Pipe.comp e28 (Pipe.comp e29 (Pipe.comp e30 (e31))))))))))))))))))))))))))))))
  have hT0 : W0 = [Val.int ℓ] ++ buCB p α s t := by
    simp only [W0, BK, buCB, List.cons_append, List.nil_append]
  have hT31 : W31 = [Val.int (buZb p α s t ℓ), Val.int ℓ] ++ buCB p α s t := by
    simp only [W31, BK, buCB, List.cons_append, List.nil_append]
  refine Pipe.le (Pipe.rwA (Pipe.rw hmain hT31) hT0) ?_
  refine le_trans (le_of_eq ?_) (buStepCost (KS := KS) (n := 31) hp (by norm_num))
  ring

end Work.Resample
