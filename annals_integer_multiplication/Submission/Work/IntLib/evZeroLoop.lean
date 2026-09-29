import Mathlib
import Submission.Work.IntLib.evZeroDefs

/-!
# `IntLib` / `evZeroLoop`: the body and loop specification of `zLoop`

`Work.IntLib.zLoop` is the skip loop of the `evZeroChain` word: starting with the loop flag
`zFl = zGo` and stack `zStk` holding the bits of the encoding of a natural number followed by its
closing `Glyph.iend`, it pops glyphs one at a time.  Every bit glyph sets the flag back to `zGo`
(one more iteration); the `iend` glyph sets it to `zStop` and the loop stops.

We prove
* `zBody_bit` / `zBody_iend`: one iteration of the loop body in the two cases (cost exactly `3`),
* `zLoopRuns`: `bs.length + 1` iterations consuming the bits `bs` and the closing `iend`
  (cost `4 * (bs.length + 1)`),
* `evZeroLoop`: the loop, cost `4 * bs.length + 5` (the extra final test).
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- One iteration of the loop body when the top glyph of stack `zStk` is a bit: the glyph is popped
and (as it is not `Glyph.iend`) the flag `zFl` is set back to `zGo`.  Cost exactly `3`. -/
theorem zBody_bit (main : Cmd) (b : Bool) (g : Reg → Glyph) (X : Stk → List Glyph)
    (rest : List Glyph) (hX : X zStk = Glyph.bit b :: rest) :
    ∃ g₁ : Reg → Glyph, g₁ zFl = zGo ∧
      Ev main zBody ⟨g, X⟩ ⟨g₁, Function.update X zStk rest⟩ 3 := by
  have hpop : Ev main (.pop zStk zRd) ⟨g, X⟩
      ⟨Function.update g zRd (Glyph.bit b), Function.update X zStk rest⟩ 1 := by
    have h := ev_pop' main zStk zRd g X
    rw [hX] at h
    simpa using h
  have hr : (⟨Function.update g zRd (Glyph.bit b),
      Function.update X zStk rest⟩ : State).reg zRd ≠ Glyph.iend := by
    show Function.update g zRd (Glyph.bit b) zRd ≠ Glyph.iend
    rw [show Function.update g zRd (Glyph.bit b) zRd = Glyph.bit b from by simp]
    exact bit_ne_iend b
  have hset : Ev main (.set zFl zGo)
      ⟨Function.update g zRd (Glyph.bit b), Function.update X zStk rest⟩
      ⟨Function.update (Function.update g zRd (Glyph.bit b)) zFl zGo,
        Function.update X zStk rest⟩ 1 :=
    ev_set' main zFl zGo _ _
  have hite : Ev main (.ite zRd Glyph.iend (.set zFl zStop) (.set zFl zGo))
      ⟨Function.update g zRd (Glyph.bit b), Function.update X zStk rest⟩
      ⟨Function.update (Function.update g zRd (Glyph.bit b)) zFl zGo,
        Function.update X zStk rest⟩ 2 :=
    Ev.iteF hr hset
  exact ⟨_, by simp, Ev.seq hpop hite⟩

/-- One iteration of the loop body when the top glyph of stack `zStk` is `Glyph.iend`: the glyph is
popped and the flag `zFl` is set to `zStop`, so the loop stops.  Cost exactly `3`. -/
theorem zBody_iend (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (rest : List Glyph) (hX : X zStk = Glyph.iend :: rest) :
    ∃ g₁ : Reg → Glyph, g₁ zFl = zStop ∧
      Ev main zBody ⟨g, X⟩ ⟨g₁, Function.update X zStk rest⟩ 3 := by
  have hpop : Ev main (.pop zStk zRd) ⟨g, X⟩
      ⟨Function.update g zRd Glyph.iend, Function.update X zStk rest⟩ 1 := by
    have h := ev_pop' main zStk zRd g X
    rw [hX] at h
    simpa using h
  have hset : Ev main (.set zFl zStop)
      ⟨Function.update g zRd Glyph.iend, Function.update X zStk rest⟩
      ⟨Function.update (Function.update g zRd Glyph.iend) zFl zStop,
        Function.update X zStk rest⟩ 1 :=
    ev_set' main zFl zStop _ _
  have hite : Ev main (.ite zRd Glyph.iend (.set zFl zStop) (.set zFl zGo))
      ⟨Function.update g zRd Glyph.iend, Function.update X zStk rest⟩
      ⟨Function.update (Function.update g zRd Glyph.iend) zFl zStop,
        Function.update X zStk rest⟩ 2 :=
    Ev.iteT (by simp) hset
  exact ⟨_, by simp, Ev.seq hpop hite⟩

/-- `zLoop` starting with the flag `zGo` and handling the glyph sequence
`bs.map Glyph.bit ++ Glyph.iend :: rest` on stack `zStk` runs `bs.length + 1` iterations: it pops
all bits and the closing `iend`, leaving `rest` on `zStk` and the flag at `zStop`.
Cost exactly `4 * (bs.length + 1)`. -/
theorem zLoopRuns (main : Cmd) :
    ∀ (bs : List Bool) (g : Reg → Glyph) (X : Stk → List Glyph) (rest : List Glyph),
      X zStk = bs.map Glyph.bit ++ Glyph.iend :: rest → g zFl = zGo →
      ∃ g' : Reg → Glyph, g' zFl = zStop ∧
        loopRuns main zFl zGo zBody (bs.length + 1) ⟨g, X⟩
          ⟨g', Function.update X zStk rest⟩ (4 * (bs.length + 1)) := by
  intro bs
  induction bs with
  | nil =>
      intro g X rest hX hg
      obtain ⟨g₁, hg₁, hb⟩ := zBody_iend main g X rest (by simpa using hX)
      exact ⟨g₁, hg₁, loopRuns.one hg hb⟩
  | cons b bs ih =>
      intro g X rest hX hg
      obtain ⟨g₁, hg₁, hb⟩ :=
        zBody_bit main b g X (bs.map Glyph.bit ++ Glyph.iend :: rest) (by simpa using hX)
      obtain ⟨g₂, hg₂, hloop⟩ :=
        ih g₁ (Function.update X zStk (bs.map Glyph.bit ++ Glyph.iend :: rest)) rest
          (by simp) hg₁
      have hupd : Function.update
            (Function.update X zStk (bs.map Glyph.bit ++ Glyph.iend :: rest)) zStk rest
          = Function.update X zStk rest := by
        funext j
        by_cases hj : j = zStk
        · subst hj; simp
        · simp [hj]
      rw [hupd] at hloop
      refine ⟨g₂, hg₂, ?_⟩
      exact loopRuns.succ' hg hb hloop (by simp; omega)

theorem evZeroLoop (main : HvdH.Cmd) (bs : List Bool) (g : HvdH.Reg → HvdH.Glyph)
    (hg : g Work.IntLib.zFl = Work.IntLib.zGo) (Y : HvdH.Stk → List HvdH.Glyph)
    (rest : List HvdH.Glyph)
    (hY : Y Work.IntLib.zStk = bs.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: rest) :
    ∃ g' : HvdH.Reg → HvdH.Glyph,
      Work.Layout.Ev main Work.IntLib.zLoop ⟨g, Y⟩
        ⟨g', Function.update Y Work.IntLib.zStk rest⟩ (4 * bs.length + 5) := by
  obtain ⟨g', hg', hrun⟩ := zLoopRuns main bs g Y rest hY hg
  have hne : (⟨g', Function.update Y zStk rest⟩ : State).reg zFl ≠ zGo := by
    show g' zFl ≠ zGo
    rw [hg']
    exact zGo_ne_zStop.symm
  obtain ⟨n, he, hl⟩ := loopRuns.eval' hrun hne
  exact ⟨g', n, he, by omega⟩

end Work.IntLib
