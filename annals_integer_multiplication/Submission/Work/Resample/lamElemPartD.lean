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

/-! ## `lamElemPartD`: steps 40--52, `V39 -> V52`

* 40: `KL.dup`
* 41: `KL.roll 2`
* 42: `IL.mulS` (`LH`)
* 43: `KL.pick 3`
* 44: `KL.roll 3`
* 45: `IL.add` (`R`)
* 46: `KL.pushVal One`
* 47: `KL.roll 3`
* 48: `KL.swap`
* 49: `IL.sub` (`N1H`)
* 50: `IL.mulS` (`Sx`)
* 51: `KL.swap`
* 52: `IL.add` (`K0`) -/

theorem lamElemPartD_aux (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Pipe main prog (V39 s t m i) (V52 s t m i) (K * (Wsz s t m i) ^ K) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨dupProg, Kd, hdup⟩ := KL.dup
  obtain ⟨pushProg, Kpu, hpush⟩ := KL.pushVal
  obtain ⟨swapProg, Ks, hswap⟩ := KL.swap
  obtain ⟨mulProg, Km, hmul⟩ := IL.mulS
  obtain ⟨addProg, Ka, hadd⟩ := IL.add
  obtain ⟨subProg, Ksub, hsub⟩ := IL.sub
  set KS : ℕ := Kpk + Kr + Kd + Kpu + Ks + Km + Ka + Ksub + 1 with hKS
  refine ⟨chainProg [dupProg, rollProg 2, mulProg, pickProg 3, rollProg 3, addProg,
      pushProg (.int (1 : ℤ)), rollProg 3, swapProg, subProg, mulProg, swapProg, addProg],
    1000000 * KS + 1000, ?_⟩
  intro main s t m i hst hm hi
  have hKS1 : 1 ≤ KS := by rw [hKS]; omega
  have hKpick : Kpk ≤ KS := by rw [hKS]; omega
  have hKroll : Kr ≤ KS := by rw [hKS]; omega
  have hKdup : Kd ≤ KS := by rw [hKS]; omega
  have hKpush : Kpu ≤ KS := by rw [hKS]; omega
  have hKswap : Ks ≤ KS := by rw [hKS]; omega
  have hKmul : Km ≤ KS := by rw [hKS]; omega
  have hKadd : Ka ≤ KS := by rw [hKS]; omega
  have hKsub : Ksub ≤ KS := by rw [hKS]; omega
  have hW9 : 9 ≤ Wsz s t m i := Wsz_ge s t m i
  have hX2 : 2 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX3 : 3 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX66 : 66 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hXo : vsz (.int (1 : ℤ)) ≤ Xsc s t m i := by
    rw [vsz_int, isz_one]; simp only [Xsc]; omega
  refine Pipe.le (Pipe.chain
      [dupProg, rollProg 2, mulProg, pickProg 3, rollProg 3, addProg,
        pushProg (.int (1 : ℤ)), rollProg 3, swapProg, subProg, mulProg, swapProg, addProg]
      [V39 s t m i, V40 s t m i, V41 s t m i, V42 s t m i, V43 s t m i, V44 s t m i,
        V45 s t m i, V46 s t m i, V47 s t m i, V48 s t m i, V49 s t m i, V50 s t m i,
        V51 s t m i, V52 s t m i]
      (CB (Xsc s t m i) KS) (by simp) ?_)
    (cost_final (n := 13) (by omega) hKS1 hW9)
  intro j hj
  have hj' : j < 13 := by simpa using hj
  clear hj
  interval_cases j
  · -- step 40: dup
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.dup (main := main) hdup (vH s t m i)))
      (le_CB_one hKdup (vsz_vH s t m i) hX2)
  · -- step 41: roll 2
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V40 s t m i) (k := 2)
        (by simp [V40]))
        (by simp only [V40, V41]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V40 s t m i hst) (by simp [V40]) hX66)
  · -- step 42: mulS LH
    exact Pipe.le (Pipe.appendTail [vH s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wL s t m i) (b := wH s t m i) trivial))
      (le_CB_mul hKmul (iszle_vL s t m i hst) (iszle_vH s t m i) hX2)
  · -- step 43: pick 3
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V42 s t m i) (k := 3)
        (by simp [V42]))
        (by simp only [V42, V43]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V42 s t m i hst) (by simp [V42]) hX66)
  · -- step 44: roll 3
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V43 s t m i) (k := 3)
        (by simp [V43]))
        (by simp only [V43, V44]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V43 s t m i hst) (by simp [V43]) hX66)
  · -- step 45: add R
    exact Pipe.le (Pipe.appendTail [vLH s t m i, vH s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hadd main) (a := wI s t m i) (b := wS s t m i) trivial))
      (le_CB_add hKadd (iszle_vI s t m i) (iszle_vS s t m i) hX2)
  · -- step 46: push One
    exact Pipe.le (Pipe.pushOnAny (main := main) (hpush main (.int (1 : ℤ)))) (le_CB_one hKpush hXo hX2)
  · -- step 47: roll 3
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V46 s t m i) (k := 3)
        (by simp [V46]))
        (by simp only [V46, V47]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V46 s t m i hst) (by simp [V46]) hX66)
  · -- step 48: swap
    exact Pipe.le (Pipe.appendTail [vR s t m i, vLH s t m i, vS s t m i, vT s t m i]
        (Pipe.swap (main := main) hswap (vH s t m i) (vOne s t m i)))
      (le_CB_two hKswap (vsz_vH s t m i) (vsz_vOne s t m i) hX3)
  · -- step 49: sub N1H
    exact Pipe.le (Pipe.appendTail [vR s t m i, vLH s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hsub main) (a := wOne s t m i) (b := wH s t m i) trivial))
      (le_CB_add hKsub (iszle_vOne s t m i) (iszle_vH s t m i) hX2)
  · -- step 50: mulS Sx
    exact Pipe.le (Pipe.appendTail [vLH s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wN1H s t m i) (b := wR s t m i) trivial))
      (le_CB_mul hKmul (iszle_vN1H s t m i) (iszle_vR s t m i) hX2)
  · -- step 51: swap
    exact Pipe.le (Pipe.appendTail [vS s t m i, vT s t m i]
        (Pipe.swap (main := main) hswap (vSx s t m i) (vLH s t m i)))
      (le_CB_two hKswap (vsz_vSx s t m i) (vsz_vLH s t m i hst) hX3)
  · -- step 52: add K0
    exact Pipe.le (Pipe.appendTail [vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hadd main) (a := wLH s t m i) (b := wSx s t m i) trivial))
      (le_CB_add hKadd (iszle_vLH s t m i hst) (iszle_vSx s t m i) hX2)

end Work.Resample.LamElem

namespace Work.Resample

open HvdH

theorem lamElemPartD (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Work.Resample.Pipe main prog (Work.Resample.LamElem.V39 s t m i)
        (Work.Resample.LamElem.V52 s t m i) (K * (Work.Resample.LamElem.Wsz s t m i) ^ K) :=
  Work.Resample.LamElem.lamElemPartD_aux KL IL

end Work.Resample
