import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.mvVal_ev_full

/-!
# One iteration of the list-walking loop

`walkBody` pops the top glyph of stack `0`; on a `cons` glyph `Glyph.cons` it moves the following
value `v` (via `mvVal`) from stack `0` to `sS`, pushes one unary unit `gU` on the counter `sD` and
sets the loop register `rG` back to `gCont_x` so that `walkProg_x` keeps going.

This file proves that single step, with its cost `16 * (vsz v + 1) + 5` and with the frame
conditions (`mvVal_ev_full` is the version of `mvVal` that also restores its own scratch stacks
`sX`, `sY`, so every stack other than `0`, `sS`, `sD` is left untouched).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Layout.Take

open HvdH

theorem walkBody_cons (main : HvdH.Cmd) (v : HvdH.Val) (A : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (h0 : X 0 = HvdH.Glyph.cons :: v.enc ++ A) (hg : g Work.Layout.rG = Work.Layout.gCont_x) : ∃ s' n, Work.Layout.Ev main Work.Layout.walkBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (HvdH.vsz v + 1) + 5 ∧ s'.stk 0 = A ∧ s'.stk Work.Layout.sS = v.enc ++ X Work.Layout.sS ∧ s'.stk Work.Layout.sD = Work.Layout.gU :: X Work.Layout.sD ∧ s'.reg Work.Layout.rG = Work.Layout.gCont_x ∧ (∀ j, j ≠ 0 → j ≠ Work.Layout.sS → j ≠ Work.Layout.sD → s'.stk j = X j) := by
  -- the stacks involved are pairwise distinct
  have hzS : (0 : Stk) ≠ sS := by decide
  have hzX : (0 : Stk) ≠ sX := by decide
  have hzY : (0 : Stk) ≠ sY := by decide
  have hSX : sS ≠ sX := by decide
  have hSY : sS ≠ sY := by decide
  have hXY : sX ≠ sY := by decide
  have hS0 : sS ≠ (0 : Stk) := by decide
  have hX0 : sX ≠ (0 : Stk) := by decide
  have hY0 : sY ≠ (0 : Stk) := by decide
  have hD0 : sD ≠ (0 : Stk) := by decide
  have hDS : sD ≠ sS := by decide
  have hDX : sD ≠ sX := by decide
  have hDY : sD ≠ sY := by decide
  -- the state produced by the initial `pop`
  have hreg0 : (Function.update g rE_x ((X 0).headD Glyph.eos)) rE_x = Glyph.cons := by
    rw [Function.update_self, h0]; rfl
  have htail0 : (Function.update X 0 ((X 0).tail)) 0 = v.enc ++ A := by
    rw [Function.update_self, h0]; rfl
  have htailS : (Function.update X 0 ((X 0).tail)) sS = X sS :=
    Function.update_of_ne hS0 _ _
  -- the value move
  obtain ⟨s₁, n₁, hEv₁, hn₁, hA, hS, hXc, hYc, hfr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := sS) (c := sX) (d := sY)
      (g := Function.update g rE_x ((X 0).headD Glyph.eos))
      (X := Function.update X 0 ((X 0).tail)) (v := v) (A := A) (B := X sS)
      hzS hzX hzY hSX hSY hXY htail0 htailS
  have hXsX : s₁.stk sX = X sX := by rw [hXc, Function.update_of_ne hX0]
  have hYsY : s₁.stk sY = X sY := by rw [hYc, Function.update_of_ne hY0]
  have hRsD : s₁.stk sD = X sD := by
    rw [hfr sD hD0 hDS hDX hDY, Function.update_of_ne hD0]
  -- then `set rE_x gU ;; push sD rE_x ;; set rG gCont_x`
  have hset : Ev main (.set rE_x gU) s₁ ⟨Function.update s₁.reg rE_x gU, s₁.stk⟩ 1 :=
    ev_set' main rE_x gU s₁.reg s₁.stk
  have hpush : Ev main (.push sD rE_x) ⟨Function.update s₁.reg rE_x gU, s₁.stk⟩
      ⟨Function.update s₁.reg rE_x gU, Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ 1 := by
    have h := ev_push' main sD rE_x (Function.update s₁.reg rE_x gU) s₁.stk
    rwa [Function.update_self] at h
  have hsetg : Ev main (.set rG gCont_x)
      ⟨Function.update s₁.reg rE_x gU, Function.update s₁.stk sD (gU :: s₁.stk sD)⟩
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ 1 :=
    ev_set' main rG gCont_x _ _
  have htail : Ev main (.seq (.set rE_x gU) (.seq (.push sD rE_x) (.set rG gCont_x))) s₁
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ 3 :=
    Ev.seq' hset (Ev.seq' hpush hsetg (by rfl)) (by rfl)
  -- the whole `then` branch
  have hbranch : Ev main
      (.seq (mvVal 0 sS sX sY) (.seq (.set rE_x gU) (.seq (.push sD rE_x) (.set rG gCont_x))))
      ⟨Function.update g rE_x ((X 0).headD Glyph.eos), Function.update X 0 ((X 0).tail)⟩
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ (n₁ + 3) :=
    Ev.seq' hEv₁ htail (by rfl)
  have hite : Ev main (.ite rE_x Glyph.cons
        (.seq (mvVal 0 sS sX sY) (.seq (.set rE_x gU) (.seq (.push sD rE_x) (.set rG gCont_x))))
        (.set rG Glyph.eos))
      ⟨Function.update g rE_x ((X 0).headD Glyph.eos), Function.update X 0 ((X 0).tail)⟩
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ (n₁ + 3 + 1) :=
    Ev.iteT hreg0 hbranch
  have hpop : Ev main (.pop 0 rE_x) ⟨g, X⟩
      ⟨Function.update g rE_x ((X 0).headD Glyph.eos), Function.update X 0 ((X 0).tail)⟩ 1 :=
    ev_pop' main 0 rE_x g X
  have hbody : Ev main
      (.seq (.pop 0 rE_x)
        (.ite rE_x Glyph.cons
          (.seq (mvVal 0 sS sX sY) (.seq (.set rE_x gU) (.seq (.push sD rE_x) (.set rG gCont_x))))
          (.set rG Glyph.eos))) ⟨g, X⟩
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ (1 + (n₁ + 3 + 1)) :=
    Ev.seq' hpop hite (by rfl)
  have hmain : Ev main walkBody ⟨g, X⟩
      ⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ (1 + (n₁ + 3 + 1)) := by
    unfold walkBody
    exact hbody
  refine ⟨⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
      Function.update s₁.stk sD (gU :: s₁.stk sD)⟩, 1 + (n₁ + 3 + 1), hmain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · show Function.update s₁.stk sD (gU :: s₁.stk sD) 0 = A
    rw [Function.update_of_ne hD0.symm, hA]
  · show Function.update s₁.stk sD (gU :: s₁.stk sD) sS = v.enc ++ X sS
    rw [Function.update_of_ne hDS.symm, hS]
  · show Function.update s₁.stk sD (gU :: s₁.stk sD) sD = gU :: X sD
    rw [Function.update_self, hRsD]
  · show Function.update (Function.update s₁.reg rE_x gU) rG gCont_x rG = gCont_x
    rw [Function.update_self]
  · intro j hj0 hjS hjD
    have hj : (⟨Function.update (Function.update s₁.reg rE_x gU) rG gCont_x,
        Function.update s₁.stk sD (gU :: s₁.stk sD)⟩ : State).stk j = s₁.stk j := by
      show Function.update s₁.stk sD (gU :: s₁.stk sD) j = s₁.stk j
      exact Function.update_of_ne hjD _ _
    rw [hj]
    rcases eq_or_ne j sX with rfl | hjX
    · rw [hXsX]
    · rcases eq_or_ne j sY with rfl | hjY
      · rw [hYsY]
      · rw [hfr j hj0 hjS hjX hjY, Function.update_of_ne hj0]

end Work.Layout.Take
