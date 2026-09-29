import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Layout.Take

open HvdH
open Work.Layout

/-- `n ≤ ys.length → n ≤ sum of the sizes of the first `n` values`. -/
theorem le_sum_vsz_take (ys : List Val) (n : ℕ) (hn : n ≤ ys.length) :
    n ≤ ((ys.take n).map vsz).sum := by
  have hlen : (ys.take n).length = n := by rw [List.length_take, Nat.min_eq_left hn]
  have hle : (ys.take n).length ≤ ((ys.take n).map vsz).sum := by
    have h : ((ys.take n).map vsz).length ≤ ((ys.take n).map vsz).sum :=
      List.length_le_sum_of_one_le _ (by
        intro i hi
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hi
        exact one_le_vsz v)
    simpa using h
  omega

/-- One iteration of the shift loop when a unit is available: move the top element of `sS` to
`sT_x`, consume one unit of `sD`, keep `rG = gCont_x`. -/
theorem shiftBody_go (main : Cmd) {v : Val} {S T D : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (hS : X sS = v.enc ++ S) (hT : X sT_x = T) (hD : X sD = gU :: D)
    (_hg : g rG = gCont_x) :
    ∃ s' n, Ev main shiftBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) + 4 ∧
      s'.stk sS = S ∧ s'.stk sT_x = v.enc ++ T ∧ s'.stk sD = D ∧ s'.reg rG = gCont_x ∧
      s'.stk sX = X sX ∧ s'.stk sY = X sY ∧
      (∀ j, j ≠ sS → j ≠ sT_x → j ≠ sD → j ≠ sX → j ≠ sY → s'.stk j = X j) := by
  have hpeek : Ev main (.peek sD rE_x) ⟨g, X⟩ ⟨Function.update g rE_x gU, X⟩ 1 := by
    have h := ev_peek' main sD rE_x g X
    rw [hD] at h
    simpa using h
  have hpop : Ev main (.pop sD rE_x) ⟨Function.update g rE_x gU, X⟩
      ⟨Function.update g rE_x gU, Function.update X sD D⟩ 1 := by
    have h := ev_pop' main sD rE_x (Function.update g rE_x gU) X
    rw [hD] at h
    simpa using h
  obtain ⟨s2, n2, hmv, hnmv, hS2, hT2, hX2, hY2, hfr2⟩ :=
    mvVal_ev_full (main := main) (a := sS) (b := sT_x) (c := sX) (d := sY)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update g rE_x gU) (X := Function.update X sD D) (v := v) (A := S) (B := T)
      (by rw [Function.update_of_ne (by decide : sS ≠ sD), hS])
      (by rw [Function.update_of_ne (by decide : sT_x ≠ sD), hT])
  have hX2' : s2.stk sX = X sX := by
    rw [hX2, Function.update_of_ne (by decide : sX ≠ sD)]
  have hY2' : s2.stk sY = X sY := by
    rw [hY2, Function.update_of_ne (by decide : sY ≠ sD)]
  have hD2 : s2.stk sD = D := by
    rw [hfr2 sD (by decide) (by decide) (by decide) (by decide), Function.update_self]
  have hset : Ev main (.set rG gCont_x) ⟨s2.reg, s2.stk⟩
      ⟨Function.update s2.reg rG gCont_x, s2.stk⟩ 1 := ev_set' main rG gCont_x s2.reg s2.stk
  have hA : Ev main (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x])
      ⟨Function.update g rE_x gU, X⟩
      ⟨Function.update s2.reg rG gCont_x, s2.stk⟩ (1 + (n2 + 1)) :=
    Ev.seqs_cons (cs := [mvVal sS sT_x sX sY, .set rG gCont_x]) hpop
      (Ev.seqs_cons (cs := [.set rG gCont_x]) hmv hset)
  have hite : Ev main (.ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x])
        (.set rG Glyph.eos)) ⟨Function.update g rE_x gU, X⟩
      ⟨Function.update s2.reg rG gCont_x, s2.stk⟩ (1 + (n2 + 1) + 1) :=
    Ev.iteT (by simp) hA
  have hbody : Ev main (seqs [.peek sD rE_x,
        .ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x]) (.set rG Glyph.eos)])
      ⟨g, X⟩ ⟨Function.update s2.reg rG gCont_x, s2.stk⟩
      (1 + (1 + (n2 + 1) + 1)) :=
    Ev.seqs_cons (cs := [.ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x])
        (.set rG Glyph.eos)]) hpeek hite
  refine ⟨_, _, hbody, by omega, hS2, hT2, hD2, ?_, hX2', hY2', ?_⟩
  · simp
  · intro j hjS hjT hjD hjX hjY
    show s2.stk j = X j
    rw [hfr2 j hjS hjT hjX hjY, Function.update_of_ne hjD]

/-- One iteration of the shift loop when no unit is left (the top of `sD` is the frame marker):
do nothing but stop (`rG := eos`). -/
theorem shiftBody_stop (main : Cmd) {D : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hD : X sD = gMark :: D) :
    ∃ s' n, Ev main shiftBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk sS = X sS ∧ s'.stk sT_x = X sT_x ∧ s'.stk sD = X sD ∧ s'.reg rG = Glyph.eos ∧
      (∀ j, s'.stk j = X j) := by
  have hpeek : Ev main (.peek sD rE_x) ⟨g, X⟩ ⟨Function.update g rE_x gMark, X⟩ 1 := by
    have h := ev_peek' main sD rE_x g X
    rw [hD] at h
    simpa using h
  have hne : (Function.update g rE_x gMark) rE_x ≠ gU := by
    rw [Function.update_self]; exact gMark_ne_gU
  have hset : Ev main (.set rG Glyph.eos) ⟨Function.update g rE_x gMark, X⟩
      ⟨Function.update (Function.update g rE_x gMark) rG Glyph.eos, X⟩ 1 :=
    ev_set' main rG Glyph.eos _ _
  have hite : Ev main (.ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x])
        (.set rG Glyph.eos)) ⟨Function.update g rE_x gMark, X⟩
      ⟨Function.update (Function.update g rE_x gMark) rG Glyph.eos, X⟩ 2 :=
    Ev.iteF hne hset
  have hbody : Ev main (seqs [.peek sD rE_x,
        .ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x]) (.set rG Glyph.eos)])
      ⟨g, X⟩ ⟨Function.update (Function.update g rE_x gMark) rG Glyph.eos, X⟩ 3 :=
    Ev.seqs_cons (cs := [.ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x])
        (.set rG Glyph.eos)]) hpeek hite
  refine ⟨_, _, hbody, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp
  · intro j; rfl

/-- The shift loop: it makes `n + 1` iterations (the last one only stops), moving the first `n`
elements of `ys` from `sS` to `sT_x` (reversed, so the last one is on top) and consuming the `n`
units of `sD`. -/
theorem shiftLoop (main : Cmd) :
    ∀ (n : ℕ) (ys : List Val), n ≤ ys.length →
      ∀ (Srest Trest Drest : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
        X sS = encs ys ++ gMark :: Srest → X sT_x = Trest →
        X sD = List.replicate n gU ++ gMark :: Drest → g rG = gCont_x →
        ∃ s', loopRuns main rG gCont_x shiftBody (n + 1) ⟨g, X⟩ s'
            (16 * (((ys.take n).map vsz).sum) + 21 * n + 4) ∧
          s'.stk sS = encs (ys.drop n) ++ gMark :: Srest ∧
          s'.stk sT_x = encs ((ys.take n).reverse) ++ Trest ∧
          s'.stk sD = gMark :: Drest ∧ s'.reg rG = Glyph.eos ∧
          s'.stk sX = X sX ∧ s'.stk sY = X sY ∧
          (∀ j, j ≠ sS → j ≠ sT_x → j ≠ sD → j ≠ sX → j ≠ sY → s'.stk j = X j) := by
  intro n
  induction n with
  | zero =>
      intro ys _ Srest Trest Drest g X hS hT hD hg
      have hD0 : X sD = gMark :: Drest := by simpa using hD
      obtain ⟨s', n', hev, hn', hS', hT', hD', hrG, hfr⟩ :=
        shiftBody_stop main (D := Drest) (g := g) (X := X) hD0
      refine ⟨s', loopRuns.mono (by omega) (loopRuns.one hg (hev.mono hn')) (by omega),
        ?_, ?_, ?_, hrG, ?_, ?_, ?_⟩
      · rw [hS', hS]; simp
      · rw [hT', hT]; simp [Work.Kernel.encs_nil]
      · rw [hD', hD0]
      · rw [hfr sX]
      · rw [hfr sY]
      · intro j _ _ _ _ _
        exact hfr j
  | succ n ih =>
      intro ys hn Srest Trest Drest g X hS hT hD hg
      cases ys with
      | nil => simp at hn
      | cons v rest =>
        have hn' : n ≤ rest.length := by simp only [List.length_cons] at hn; omega
        have hS1in : X sS = v.enc ++ (encs rest ++ gMark :: Srest) := by
          rw [hS, Work.Kernel.encs_cons, List.append_assoc]
        have hD1in : X sD = gU :: (List.replicate n gU ++ gMark :: Drest) := by
          rw [hD, List.replicate_succ, List.cons_append]
        obtain ⟨s1, m1, hev1, hm1, hS1, hT1, hD1, hr1, hX1, hY1, hfr1⟩ :=
          shiftBody_go main (v := v) (S := encs rest ++ gMark :: Srest) (T := Trest)
            (D := List.replicate n gU ++ gMark :: Drest) (g := g) (X := X) hS1in hT hD1in hg
        obtain ⟨s2, hrun2, hS2, hT2, hD2, hr2, hX2, hY2, hfr2⟩ :=
          ih rest hn' Srest (v.enc ++ Trest) Drest s1.reg s1.stk hS1 hT1 hD1 hr1
        have hcat := loopRuns.concat (n + 1) (loopRuns.one hg (hev1.mono hm1)) hrun2
        have hcost : (16 * (vsz v + 1) + 4 + 1) + (16 * ((rest.take n).map vsz).sum + 21 * n + 4) ≤
            16 * ((((v :: rest).take (n + 1)).map vsz).sum) + 21 * (n + 1) + 4 := by
          rw [List.take_succ_cons, List.map_cons, List.sum_cons]
          omega
        refine ⟨s2, loopRuns.mono (by omega) (loopRuns.cast (by omega) hcat) hcost,
          ?_, ?_, hD2, hr2, ?_, ?_, ?_⟩
        · rw [List.drop_succ_cons]; exact hS2
        · rw [List.take_succ_cons, List.reverse_cons, Work.Kernel.encs_append,
            Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil, List.append_assoc]
          exact hT2
        · rw [hX2, hX1]
        · rw [hY2, hY1]
        · intro j hjS hjT hjD hjX hjY
          rw [hfr2 j hjS hjT hjD hjX hjY, hfr1 j hjS hjT hjD hjX hjY]

/-- `shiftProg` (`Submission/Work/Layout/Take/Defs.lean`) consumes `n` unary units from `sD` (all
counters are above a `gMark` frame marker) and moves one element of `sS` to `sT_x` per unit; `sS`
shows `ys` (its top element is `ys[0]`) and the loop moves `ys.take n` off it, so `sS` shows
`ys.drop n` afterwards and `sT_x` receives `(ys.take n).reverse` (the last element moved is on top).
`sD` keeps its marker.

Useful: `Work.Layout.mvVal_ev` (in `Submission/Work/Layout/Move.lean`) moves one value from `sS`
to `sT_x`; it restores its own scratch stacks `sX`, `sY` only through `mvA_ev`/`mvB_ev` (see the
proof of `mvVal_ev`, or the stronger `mvVal_ev_full` if it is in the workspace), so a stronger
variant may have to be proved.  Also `HvdH.encs_append`, `Work.Layout.one_le_vsz`, the `Ev`
primitives of `Submission/Work/Layout/Base.lean`. -/
theorem shift_ev (main : HvdH.Cmd) (ys : List HvdH.Val) (n : ℕ) (hn : n ≤ ys.length)
    (Srest Trest Drest : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph)
    (hS : X Work.Layout.sS = HvdH.encs ys ++ Work.Layout.gMark :: Srest)
    (hT : X Work.Layout.sT_x = Trest)
    (hD : X Work.Layout.sD = List.replicate n Work.Layout.gU ++ Work.Layout.gMark :: Drest) :
    ∃ s' m, Work.Layout.Ev main Work.Layout.shiftProg ⟨g, X⟩ s' m ∧
      m ≤ 20 * (((ys.take n).map HvdH.vsz).sum + n + 1) ∧
      s'.stk Work.Layout.sS = HvdH.encs (ys.drop n) ++ Work.Layout.gMark :: Srest ∧
      s'.stk Work.Layout.sT_x = HvdH.encs ((ys.take n).reverse) ++ Trest ∧
      s'.stk Work.Layout.sD = Work.Layout.gMark :: Drest ∧
      (∀ j, j ≠ Work.Layout.sS → j ≠ Work.Layout.sT_x → j ≠ Work.Layout.sD → s'.stk j = X j) := by
  have hset : Ev main (.set rG gCont_x) ⟨g, X⟩ ⟨Function.update g rG gCont_x, X⟩ 1 :=
    ev_set' main rG gCont_x g X
  obtain ⟨s1, hrun, hS1, hT1, hD1, hr1, hX1, hY1, hfr1⟩ :=
    shiftLoop main n ys hn Srest Trest Drest (Function.update g rG gCont_x) X hS hT hD (by simp)
  have hloop : Ev main (.loop rG gCont_x shiftBody) ⟨Function.update g rG gCont_x, X⟩ s1
      (16 * (((ys.take n).map vsz).sum) + 21 * n + 4 + 1) :=
    loopRuns.eval hrun (by rw [hr1]; decide)
  have hmain : Ev main (seqs [.set rG gCont_x, .loop rG gCont_x shiftBody]) ⟨g, X⟩ s1
      (1 + (16 * (((ys.take n).map vsz).sum) + 21 * n + 4 + 1)) :=
    Ev.seqs_cons (cs := [.loop rG gCont_x shiftBody]) hset hloop
  refine ⟨s1, _, hmain, ?_, hS1, hT1, hD1, ?_⟩
  · have hsum := le_sum_vsz_take ys n hn
    omega
  · intro j hjS hjT hjD
    by_cases hjX : j = sX
    · rw [hjX]; exact hX1
    · by_cases hjY : j = sY
      · rw [hjY]; exact hY1
      · exact hfr1 j hjS hjT hjD hjX hjY

end Work.Layout.Take
