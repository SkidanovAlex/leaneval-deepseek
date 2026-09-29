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
private theorem unconsVPipe {main prog : Cmd} {K : ℕ}
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

/-! ## `lamElemPartB`: steps 16--29 -/

theorem lamElemPartB (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Pipe main prog (V15 s t m i) (V29 s t m i) (K * (Wsz s t m i) ^ K) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨dupProg, Kd, hdup⟩ := KL.dup
  obtain ⟨pushProg, Kpu, hpush⟩ := KL.pushVal
  obtain ⟨swapProg, Ks, hswap⟩ := KL.swap
  obtain ⟨mulProg, Km, hmul⟩ := IL.mulS
  obtain ⟨subProg, Ksub, hsub⟩ := IL.sub
  obtain ⟨negProg, Kneg, hneg⟩ := IL.neg
  obtain ⟨ltProg, Klt, hlt⟩ := IL.lt
  set KS : ℕ := Kpk + Kr + Kd + Kpu + Ks + Km + Ksub + Kneg + Klt + 1 with hKS
  refine ⟨chainProg [dupProg, pickProg 5, mulProg, rollProg 2, swapProg, subProg, pushProg (.int (2 : ℤ)), mulProg, dupProg, pushProg (.int (1 : ℤ)), pickProg 5, negProg, subProg, ltProg], 1000000 * KS + 1000, ?_⟩
  intro main s t m i hst hm hi
  have hKS1 : 1 ≤ KS := by rw [hKS]; omega
  have hKpick : Kpk ≤ KS := by rw [hKS]; omega
  have hKroll : Kr ≤ KS := by rw [hKS]; omega
  have hKdup : Kd ≤ KS := by rw [hKS]; omega
  have hKpush : Kpu ≤ KS := by rw [hKS]; omega
  have hKswap : Ks ≤ KS := by rw [hKS]; omega
  have hKmul : Km ≤ KS := by rw [hKS]; omega
  have hKsub : Ksub ≤ KS := by rw [hKS]; omega
  have hKneg : Kneg ≤ KS := by rw [hKS]; omega
  have hKlt : Klt ≤ KS := by rw [hKS]; omega
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
  refine Pipe.le (Pipe.chain [dupProg, pickProg 5, mulProg, rollProg 2, swapProg, subProg, pushProg (.int (2 : ℤ)), mulProg, dupProg, pushProg (.int (1 : ℤ)), pickProg 5, negProg, subProg, ltProg]
      [V15 s t m i, V16 s t m i, V17 s t m i, V18 s t m i, V19 s t m i, V20 s t m i, V21 s t m i, V22 s t m i, V23 s t m i, V24 s t m i, V25 s t m i, V26 s t m i, V27 s t m i, V28 s t m i, V29 s t m i] (CB (Xsc s t m i) KS) (by simp) ?_)
    (cost_final (n := 14) (by omega) hKS1 hW9)
  intro j hj
  have hj' : j < 14 := by simpa using hj
  clear hj
  interval_cases j
  · -- step 16: dup 
    exact Pipe.le (Pipe.appendTail [vA s t m i, vI s t m i, vS s t m i, vT s t m i] (Pipe.dup (main := main) hdup (vL s t m i)))
      (le_CB_one hKdup (vsz_vL s t m i hst) hX2)
  · -- step 17: pick 5
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V16 s t m i) (k := 5)
        (by simp [V16]))
        (by simp only [V16, V17]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V16 s t m i hst) (by simp [V16]) hX66)
  · -- step 18: mul F
    exact Pipe.le (Pipe.appendTail [vL s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wT s t m i) (b := wL s t m i) trivial))
      (le_CB_mul hKmul (iszle_vT s t m i) (iszle_vL s t m i hst) hX2)
  · -- step 19: roll 2
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V18 s t m i) (k := 2)
        (by simp [V18]))
        (by simp only [V18, V19]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V18 s t m i hst) (by simp [V18]) hX66)
  · -- step 20: swap 
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.swap (main := main) hswap (vA s t m i) (vF s t m i)))
      (le_CB_two hKswap (vsz_vA s t m i) (vsz_vF s t m i hst) hX3)
  · -- step 21: sub G
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hsub main) (a := wF s t m i) (b := wA s t m i) trivial))
      (le_CB_add hKsub (iszle_vF s t m i hst) (iszle_vA s t m i) hX2)
  · -- step 22: push Two
    exact Pipe.le (Pipe.pushOnAny (main := main) (hpush main (.int (2 : ℤ)))) (le_CB_one hKpush hXt hX2)
  · -- step 23: mul D
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wTwo s t m i) (b := wG s t m i) trivial))
      (le_CB_mul hKmul (iszle_vTwo s t m i) (iszle_vG s t m i hst) hX2)
  · -- step 24: dup 
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i] (Pipe.dup (main := main) hdup (vD s t m i)))
      (le_CB_one hKdup (vsz_vD s t m i hst) hX2)
  · -- step 25: push One
    exact Pipe.le (Pipe.pushOnAny (main := main) (hpush main (.int (1 : ℤ)))) (le_CB_one hKpush hXo hX2)
  · -- step 26: pick 5
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V25 s t m i) (k := 5)
        (by simp [V25]))
        (by simp only [V25, V26]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V25 s t m i hst) (by simp [V25]) hX66)
  · -- step 27: neg NS
    exact Pipe.le (Pipe.appendTail [vOne s t m i, vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.unOp (main := main) (hneg main) (a := wS s t m i) trivial))
      (le_CB_un1 hKneg (iszle_vS s t m i) hX1)
  · -- step 28: sub NS1
    exact Pipe.le (Pipe.appendTail [vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hsub main) (a := wNS s t m i) (b := wOne s t m i) trivial))
      (le_CB_add hKsub (iszle_vNS s t m i) (iszle_vOne s t m i) hX2)
  · -- step 29: lt Q1
    exact Pipe.le (Pipe.appendTail [vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hlt main) (a := wNS1 s t m i) (b := wD s t m i) trivial))
      (le_CB_add hKlt (iszle_vNS1 s t m i) (iszle_vD s t m i hst) hX2)


end Work.Resample.LamElem
