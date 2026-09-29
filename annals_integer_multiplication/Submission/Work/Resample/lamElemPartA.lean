import Mathlib
import Submission.Work.Resample.lamElemKit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Resample.LamElem

open HvdH
open Work.Fx

/-- `unconsV` on a one-value window. -/
theorem unconsVPipe {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b r, vs = .cons a b :: r)
      (fun vs out => ∃ a b r, vs = .cons a b :: r ∧ out = a :: b :: r) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have hc : Val.cons a' b' = Val.cons a b := (List.cons.inj (hvs'.symm.trans hv)).1
  have ht : r' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have h1 : a' = a := (Val.cons.inj hc).1
  have h2 : b' = b := (Val.cons.inj hc).2
  exact ⟨out, s', n, by rw [hout, h1, h2, ht]; rfl, hev, hn, hstk, hoth⟩

/-! ## `lamElemPartA`: steps 1--15 -/

theorem lamElemPartA (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Pipe main prog (V0 s t m i) (V15 s t m i) (K * (Wsz s t m i) ^ K) := by
  obtain ⟨ucProg, Kuc, huc⟩ := KL.unconsV
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨dupProg, Kd, hdup⟩ := KL.dup
  obtain ⟨pushProg, Kpu, hpush⟩ := KL.pushVal
  obtain ⟨swapProg, Ks, hswap⟩ := KL.swap
  obtain ⟨mulProg, Km, hmul⟩ := IL.mulS
  obtain ⟨addProg, Ka, hadd⟩ := IL.add
  obtain ⟨fdivProg, Kfd, hfd⟩ := IL.fdiv
  set KS : ℕ := Kuc + Kpk + Kr + Kd + Kpu + Ks + Km + Ka + Kfd + 1 with hKS
  refine ⟨chainProg [ucProg, rollProg 1, pickProg 2, mulProg, dupProg, pushProg (.int (2 : ℤ)), mulProg, pickProg 4, swapProg, addProg, pickProg 4, pushProg (.int (2 : ℤ)), mulProg, swapProg, fdivProg], 1000000 * KS + 1000, ?_⟩
  intro main s t m i hst hm hi
  have hKS1 : 1 ≤ KS := by rw [hKS]; omega
  have hKuc : Kuc ≤ KS := by rw [hKS]; omega
  have hKpick : Kpk ≤ KS := by rw [hKS]; omega
  have hKroll : Kr ≤ KS := by rw [hKS]; omega
  have hKdup : Kd ≤ KS := by rw [hKS]; omega
  have hKpush : Kpu ≤ KS := by rw [hKS]; omega
  have hKswap : Ks ≤ KS := by rw [hKS]; omega
  have hKmul : Km ≤ KS := by rw [hKS]; omega
  have hKadd : Ka ≤ KS := by rw [hKS]; omega
  have hKfdiv : Kfd ≤ KS := by rw [hKS]; omega
  have hW9 : 9 ≤ Wsz s t m i := Wsz_ge s t m i
  have hX1 : 1 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX2 : 2 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX3 : 3 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX66 : 66 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hXt : vsz (.int (2 : ℤ)) ≤ Xsc s t m i := by
    rw [vsz_int, isz_two]; simp only [Xsc]; omega
  have hXo : vsz (.int (1 : ℤ)) ≤ Xsc s t m i := by
    rw [vsz_int, isz_one]; simp only [Xsc]; omega
  have hpE : 0 < wE s t m i := by
    have ht : (0 : ℤ) < (t : ℤ) := by exact_mod_cast (by omega : 0 < t)
    simp only [wE, wTwo, wT]; linarith
  refine Pipe.le (Pipe.chain [ucProg, rollProg 1, pickProg 2, mulProg, dupProg, pushProg (.int (2 : ℤ)), mulProg, pickProg 4, swapProg, addProg, pickProg 4, pushProg (.int (2 : ℤ)), mulProg, swapProg, fdivProg]
      [V0 s t m i, V1 s t m i, V2 s t m i, V3 s t m i, V4 s t m i, V5 s t m i, V6 s t m i, V7 s t m i, V8 s t m i, V9 s t m i, V10 s t m i, V11 s t m i, V12 s t m i, V13 s t m i, V14 s t m i, V15 s t m i] (CB (Xsc s t m i) KS) (by simp) ?_)
    (cost_final (n := 15) (by omega) hKS1 hW9)
  intro j hj
  have hj' : j < 15 := by simpa using hj
  clear hj
  interval_cases j
  · -- step 1: uncons 
    exact Pipe.le (Pipe.appendTail [vS s t m i, vT s t m i]
        (unconsVPipe (main := main) huc (vI s t m i) (vM s t m i))) (le_CB_const hKuc hX1)
  · -- step 2: roll 1
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V1 s t m i) (k := 1)
        (by simp [V1]))
        (by simp only [V1, V2]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V1 s t m i hst) (by simp [V1]) hX66)
  · -- step 3: pick 2
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V2 s t m i) (k := 2)
        (by simp [V2]))
        (by simp only [V2, V3]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V2 s t m i hst) (by simp [V2]) hX66)
  · -- step 4: mul A
    exact Pipe.le (Pipe.appendTail [vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wS s t m i) (b := wM s t m i) trivial))
      (le_CB_mul hKmul (iszle_vS s t m i) (iszle_vM s t m i) hX2)
  · -- step 5: dup 
    exact Pipe.le (Pipe.appendTail [vI s t m i, vS s t m i, vT s t m i] (Pipe.dup (main := main) hdup (vA s t m i)))
      (le_CB_one hKdup (vsz_vA s t m i) hX2)
  · -- step 6: push Two
    exact Pipe.le (Pipe.pushOnAny (main := main) (hpush main (.int (2 : ℤ)))) (le_CB_one hKpush hXt hX2)
  · -- step 7: mul B
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wTwo s t m i) (b := wA s t m i) trivial))
      (le_CB_mul hKmul (iszle_vTwo s t m i) (iszle_vA s t m i) hX2)
  · -- step 8: pick 4
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V7 s t m i) (k := 4)
        (by simp [V7]))
        (by simp only [V7, V8]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V7 s t m i hst) (by simp [V7]) hX66)
  · -- step 9: swap 
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.swap (main := main) hswap (vT s t m i) (vB s t m i)))
      (le_CB_two hKswap (vsz_vT s t m i) (vsz_vB s t m i) hX3)
  · -- step 10: add C
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hadd main) (a := wB s t m i) (b := wT s t m i) trivial))
      (le_CB_add hKadd (iszle_vB s t m i) (iszle_vT s t m i) hX2)
  · -- step 11: pick 4
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V10 s t m i) (k := 4)
        (by simp [V10]))
        (by simp only [V10, V11]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V10 s t m i hst) (by simp [V10]) hX66)
  · -- step 12: push Two
    exact Pipe.le (Pipe.pushOnAny (main := main) (hpush main (.int (2 : ℤ)))) (le_CB_one hKpush hXt hX2)
  · -- step 13: mul E
    exact Pipe.le (Pipe.appendTail [vC s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wTwo s t m i) (b := wT s t m i) trivial))
      (le_CB_mul hKmul (iszle_vTwo s t m i) (iszle_vT s t m i) hX2)
  · -- step 14: swap 
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.swap (main := main) hswap (vE s t m i) (vC s t m i)))
      (le_CB_two hKswap (vsz_vE s t m i) (vsz_vC s t m i) hX3)
  · -- step 15: fdiv L
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hfd main) (a := wC s t m i) (b := wE s t m i) hpE))
      (le_CB_mul hKfdiv (iszle_vC s t m i) (iszle_vE s t m i) hX2)


end Work.Resample.LamElem
