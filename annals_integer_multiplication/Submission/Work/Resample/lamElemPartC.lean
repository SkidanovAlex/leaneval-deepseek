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

/-! ## `lamElemPartC`: steps 30--39, `V29 -> V39`

* 30: `KL.pick 4`
* 31: `KL.roll 2`
* 32: `IL.lt` (`Q2`)
* 33: `KL.pick 4`
* 34: `KL.pick 3`
* 35: `IL.lt` (`Q3`)
* 36: `KL.roll 1`
* 37: `KL.roll 2`
* 38: `IL.mulS` (`H12`)
* 39: `IL.mulS` (`H`) -/

theorem lamElemPartC_aux (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Pipe main prog (V29 s t m i) (V39 s t m i) (K * (Wsz s t m i) ^ K) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨mulProg, Km, hmul⟩ := IL.mulS
  obtain ⟨ltProg, Klt, hlt⟩ := IL.lt
  set KS : ℕ := Kpk + Kr + Km + Klt + 1 with hKS
  refine ⟨chainProg [pickProg 4, rollProg 2, ltProg, pickProg 4, pickProg 3, ltProg,
      rollProg 1, rollProg 2, mulProg, mulProg], 1000000 * KS + 1000, ?_⟩
  intro main s t m i hst hm hi
  have hKS1 : 1 ≤ KS := by rw [hKS]; omega
  have hKpick : Kpk ≤ KS := by rw [hKS]; omega
  have hKroll : Kr ≤ KS := by rw [hKS]; omega
  have hKmul : Km ≤ KS := by rw [hKS]; omega
  have hKlt : Klt ≤ KS := by rw [hKS]; omega
  have hW9 : 9 ≤ Wsz s t m i := Wsz_ge s t m i
  have hX2 : 2 ≤ Xsc s t m i := by simp only [Xsc]; omega
  have hX66 : 66 ≤ Xsc s t m i := by simp only [Xsc]; omega
  -- `isz` bounds of the operands of the arithmetic steps, derived from the `vsz` bounds.
  have hzD : isz (wD s t m i) ≤ Xsc s t m i := by
    simpa only [vD, vsz_int] using vsz_vD s t m i hst
  have hzS : isz (wS s t m i) ≤ Xsc s t m i := by
    simpa only [vS, vsz_int] using vsz_vS s t m i
  have hzL : isz (wL s t m i) ≤ Xsc s t m i := by
    simpa only [vL, vsz_int] using vsz_vL s t m i hst
  have hzQ1 : isz (wQ1 s t m i) ≤ Xsc s t m i := by
    simpa only [vQ1, vsz_int] using vsz_vQ1 s t m i
  have hzQ2 : isz (wQ2 s t m i) ≤ Xsc s t m i := by
    simpa only [vQ2, vsz_int] using vsz_vQ2 s t m i
  have hzQ3 : isz (wQ3 s t m i) ≤ Xsc s t m i := by
    simpa only [vQ3, vsz_int] using vsz_vQ3 s t m i
  have hzH12 : isz (wH12 s t m i) ≤ Xsc s t m i := by
    simpa only [vH12, vsz_int] using vsz_vH12 s t m i
  refine Pipe.le (Pipe.chain
      [pickProg 4, rollProg 2, ltProg, pickProg 4, pickProg 3, ltProg,
        rollProg 1, rollProg 2, mulProg, mulProg]
      [V29 s t m i, V30 s t m i, V31 s t m i, V32 s t m i, V33 s t m i, V34 s t m i,
        V35 s t m i, V36 s t m i, V37 s t m i, V38 s t m i, V39 s t m i]
      (CB (Xsc s t m i) KS) (by simp) ?_)
    (cost_final (n := 10) (by omega) hKS1 hW9)
  intro j hj
  have hj' : j < 10 := by simpa using hj
  clear hj
  interval_cases j
  · -- step 30: pick 4
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V29 s t m i) (k := 4)
        (by simp [V29]))
        (by simp only [V29, V30]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V29 s t m i hst) (by simp [V29]) hX66)
  · -- step 31: roll 2
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V30 s t m i) (k := 2)
        (by simp [V30]))
        (by simp only [V30, V31]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V30 s t m i hst) (by simp [V30]) hX66)
  · -- step 32: lt Q2
    exact Pipe.le (Pipe.appendTail [vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hlt main) (a := wD s t m i) (b := wS s t m i) trivial))
      (le_CB_add hKlt hzD hzS hX2)
  · -- step 33: pick 4
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V32 s t m i) (k := 4)
        (by simp [V32]))
        (by simp only [V32, V33]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V32 s t m i hst) (by simp [V32]) hX66)
  · -- step 34: pick 3
    refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hpick (A := V33 s t m i) (k := 3)
        (by simp [V33]))
        (by simp only [V33, V34]; simp))
      (le_CB_roll hKpick (by norm_num) (sz_V33 s t m i hst) (by simp [V33]) hX66)
  · -- step 35: lt Q3
    exact Pipe.le (Pipe.appendTail [vQ2 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hlt main) (a := wL s t m i) (b := wS s t m i) trivial))
      (le_CB_add hKlt hzL hzS hX2)
  · -- step 36: roll 1
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V35 s t m i) (k := 1)
        (by simp [V35]))
        (by simp only [V35, V36]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V35 s t m i hst) (by simp [V35]) hX66)
  · -- step 37: roll 2
    refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hroll (A := V36 s t m i) (k := 2)
        (by simp [V36]))
        (by simp only [V36, V37]; simp))
      (le_CB_roll hKroll (by norm_num) (sz_V36 s t m i hst) (by simp [V36]) hX66)
  · -- step 38: mulS H12
    exact Pipe.le (Pipe.appendTail [vQ3 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wQ1 s t m i) (b := wQ2 s t m i) trivial))
      (le_CB_mul hKmul hzQ1 hzQ2 hX2)
  · -- step 39: mulS H
    exact Pipe.le (Pipe.appendTail [vL s t m i, vI s t m i, vS s t m i, vT s t m i]
        (Pipe.binOp (main := main) (hmul main) (a := wH12 s t m i) (b := wQ3 s t m i) trivial))
      (le_CB_mul hKmul hzH12 hzQ3 hX2)

end Work.Resample.LamElem

namespace Work.Resample

open HvdH

theorem lamElemPartC (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      Work.Resample.Pipe main prog (Work.Resample.LamElem.V29 s t m i)
        (Work.Resample.LamElem.V39 s t m i) (K * (Work.Resample.LamElem.Wsz s t m i) ^ K) :=
  Work.Resample.LamElem.lamElemPartC_aux KL IL

end Work.Resample
