import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg

/-!
# `SG.gcdScale`: multiply the region of `sU` by `2 ^ g`

`SG.gcdScale` (see `GcdProg.lean`) pops the unary counter `sG` (a list of `gTick` glyphs) and
pushes one `false` bit onto `sU` per tick, i.e. it appends `k` low zero bits to the bit region of
`sU`, where `k` is the number of ticks.  Reading a bit region from the top of the stack (the
convention of `Defs.lean`) this is exactly

`us ↦ List.replicate k false ++ us`.

The loop is `.loop rgF gGo body` with

`body = peek sG rgT ; if rgT = gTick then (pop sG ; push (bit false) on sU ; rgF := gGo) else (rgF := gStop)`,

so it runs exactly `k` iterations (`7` steps each: `peek` 1, `ite` 1, the three primitives 3, plus
the successful loop test 1) followed by the failing test, total `7 * k + 5` steps for the loop, and
`7 * k + 6` including the initial `rgF := gGo`.  The program touches only the stacks `sU` and `sG`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.Layout
open Work.IntLib.SG

/-- The branch of the loop body taken while the counter `sG` still holds a tick: pop the tick,
push one `false` bit onto `sU` and keep looping. -/
def gcdScaleStep : Cmd :=
  .seq (.pop sG rgT) (.seq (.set rgU (.bit false)) (.seq (.push sU rgU) (.set rgF gGo)))

/-- The body of the loop of `SG.gcdScale`. -/
def gcdScaleBody : Cmd :=
  .seq (.peek sG rgT) (.ite rgT gTick gcdScaleStep (.set rgF gStop))

/-- `SG.gcdScale` is the `gGo`-loop of `gcdScaleBody`. -/
theorem gcdScale_eq : gcdScale = .seq (.set rgF gGo) (.loop rgF gGo gcdScaleBody) := rfl

/-- Pushing one more low bit: appending `false` before `us` is the same as one more leading zero. -/
theorem replicate_false_cons (k : ℕ) (us : List Bool) :
    List.replicate k false ++ false :: us = List.replicate (k + 1) false ++ us := by
  rw [List.replicate_succ']; simp

/-- **The loop of `SG.gcdScale`.**  From a state whose `sU` region is `us` and whose `sG` holds
exactly `k` ticks (above its marker, with `bG` below), the loop terminates with `k` `false` bits
pushed onto `sU`, `sG` emptied down to its marker, the flag at `gStop`, and cost `≤ 7 k + 5`. -/
theorem gcdScaleLoop (main : Cmd) :
    ∀ (k : ℕ) (us : List Bool) (bU bG : List Glyph) (s : State),
      s.stk sU = us.map Glyph.bit ++ Glyph.mk sU :: bU →
      s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG →
      s.reg rgF = gGo →
      ∃ s' m, Eval main (.loop rgF gGo gcdScaleBody) s s' m ∧ m ≤ 7 * k + 5 ∧
        s'.stk sU = (List.replicate k false ++ us).map Glyph.bit ++ Glyph.mk sU :: bU ∧
        s'.stk sG = Glyph.mk sG :: bG ∧ s'.reg rgF = gStop := by
  intro k
  induction k with
  | zero =>
    -- `sG` holds only its marker: the loop body takes the `else` branch and stops
    intro us bU bG s hU hG hF
    have hG' : s.stk sG = Glyph.mk sG :: bG := by simpa using hG
    let s1 : State := ⟨Function.update s.reg rgT (Glyph.mk sG), s.stk⟩
    let s2 : State := ⟨Function.update s1.reg rgF gStop, s.stk⟩
    have e1 : Ev main (.peek sG rgT) s s1 1 := by
      have h := ev_peek main sG rgT s
      rw [hG'] at h
      simpa [s1] using h
    have e2 : Ev main (.set rgF gStop) s1 s2 1 := by
      have h := ev_set main rgF gStop s1
      simpa [s2] using h
    have hr1 : s1.reg rgT = Glyph.mk sG := by simp [s1]
    have hne1 : ¬ (s1.reg rgT = gTick) := by rw [hr1]; decide
    have e3 : Ev main (.ite rgT gTick gcdScaleStep (.set rgF gStop)) s1 s2 2 := Ev.iteF hne1 e2
    have ebody : Ev main gcdScaleBody s s2 3 := by
      show Ev main (.seq (.peek sG rgT) (.ite rgT gTick gcdScaleStep (.set rgF gStop))) s s2 3
      exact Ev.seq e1 e3
    have hr2 : s2.reg rgF = gStop := by simp [s2]
    have hne2 : ¬ (s2.reg rgF = gGo) := by rw [hr2]; decide
    obtain ⟨n, hn, _⟩ := Ev.loopT hF ebody (Ev.loopF hne2)
    refine ⟨s2, n, hn, by omega, ?_, ?_, ?_⟩
    · show s2.stk sU = (List.replicate 0 false ++ us).map Glyph.bit ++ Glyph.mk sU :: bU
      simpa [s2] using hU
    · show s2.stk sG = Glyph.mk sG :: bG
      simpa [s2] using hG'
    · exact hr2
  | succ k ih =>
    -- one tick: pop it, push one `false` bit on `sU`, and continue with `k` ticks
    intro us bU bG s hU hG hF
    have hG' : s.stk sG = gTick :: (List.replicate k gTick ++ Glyph.mk sG :: bG) := by
      rw [hG]; simp [List.replicate_succ]
    let G' : List Glyph := List.replicate k gTick ++ Glyph.mk sG :: bG
    have hG'' : s.stk sG = gTick :: G' := by simpa [G'] using hG'
    let s1 : State := ⟨Function.update s.reg rgT gTick, s.stk⟩
    let s2 : State := ⟨Function.update s1.reg rgT gTick, Function.update s.stk sG G'⟩
    let s3 : State := ⟨Function.update s2.reg rgU (Glyph.bit false), s2.stk⟩
    let s4 : State := ⟨s3.reg, Function.update s3.stk sU (Glyph.bit false :: s3.stk sU)⟩
    let s5 : State := ⟨Function.update s4.reg rgF gGo, s4.stk⟩
    have e1 : Ev main (.peek sG rgT) s s1 1 := by
      have h := ev_peek main sG rgT s
      rw [hG''] at h
      simpa [s1] using h
    have hs1G : s1.stk sG = gTick :: G' := by simp [s1, hG'']
    have e2 : Ev main (.pop sG rgT) s1 s2 1 := by
      have h := ev_pop main sG rgT s1
      rw [hs1G] at h
      simpa [s2] using h
    have e3 : Ev main (.set rgU (Glyph.bit false)) s2 s3 1 := by
      have h := ev_set main rgU (Glyph.bit false) s2
      simpa [s3] using h
    have h3U : s3.reg rgU = Glyph.bit false := by simp [s3]
    have e4 : Ev main (.push sU rgU) s3 s4 1 := by
      have h := ev_push main sU rgU s3
      rw [h3U] at h
      simpa [s4] using h
    have e5 : Ev main (.set rgF gGo) s4 s5 1 := by
      have h := ev_set main rgF gGo s4
      simpa [s5] using h
    have hb : Ev main gcdScaleStep s1 s5 4 := by
      show Ev main (.seq (.pop sG rgT) (.seq (.set rgU (.bit false))
        (.seq (.push sU rgU) (.set rgF gGo)))) s1 s5 4
      exact Ev.seq e2 (Ev.seq e3 (Ev.seq e4 e5))
    have hr1 : s1.reg rgT = gTick := by simp [s1]
    have eit : Ev main (.ite rgT gTick gcdScaleStep (.set rgF gStop)) s1 s5 5 :=
      Ev.iteT hr1 hb
    have ebody : Ev main gcdScaleBody s s5 6 := by
      show Ev main (.seq (.peek sG rgT) (.ite rgT gTick gcdScaleStep (.set rgF gStop))) s s5 6
      exact Ev.seq e1 eit
    have hF5 : s5.reg rgF = gGo := by simp [s5]
    have hneUS : (sU : Stk) ≠ sG := by decide
    have hneSU : (sG : Stk) ≠ sU := by decide
    have hU5 : s5.stk sU = (false :: us).map Glyph.bit ++ Glyph.mk sU :: bU := by
      simp [s5, s4, s3, s2, s1, Function.update_apply, hneUS, hneSU, ← hU, List.map_cons]
    have hG5 : s5.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
      simp [s5, s4, s3, s2, s1, Function.update_apply, hneUS, hneSU, G']
    obtain ⟨s', m', hm', hle', hsU', hsG', hreg'⟩ := ih (false :: us) bU bG s5 hU5 hG5 hF5
    obtain ⟨n, hn, _⟩ := Ev.loopT hF ebody ⟨m', hm', le_rfl⟩
    have hrep := replicate_false_cons k us
    rw [hrep] at hsU'
    exact ⟨s', n, hn, by omega, hsU', hsG', hreg'⟩

/-- **`SG.gcdScale` multiplies by `2 ^ k`.**  With `k` ticks on `sG` (above its marker) and the
region `us` on `sU`, the program appends `k` low `false` bits to `us` (i.e. multiplies the value by
`2 ^ k`), empties `sG` down to its marker, restores every other stack, and costs at most
`100 * (k + 1)` steps. -/
theorem gcdScaleEval (main : HvdH.Cmd) (k : ℕ) (us : List Bool) (bU : List HvdH.Glyph)
    (s : HvdH.State)
    (hU : s.stk Work.IntLib.SG.sU = us.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: bU)
    (hG : s.stk Work.IntLib.SG.sG
      = List.replicate k Work.IntLib.SG.gTick ++ [HvdH.Glyph.mk Work.IntLib.SG.sG]) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.gcdScale s s' m ∧ m ≤ 100 * (k + 1) ∧
      s'.stk Work.IntLib.SG.sU = (List.replicate k false ++ us).map HvdH.Glyph.bit
        ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: bU ∧
      s'.stk Work.IntLib.SG.sG = [HvdH.Glyph.mk Work.IntLib.SG.sG] ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.SG.sU → j ≠ Work.IntLib.SG.sG → s'.stk j = s.stk j) := by
  have hG' : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: ([] : List Glyph) := by
    simpa using hG
  let s0 : State := ⟨Function.update s.reg rgF gGo, s.stk⟩
  have e0 : Ev main (.set rgF gGo) s s0 1 := by
    have h := ev_set main rgF gGo s
    simpa [s0] using h
  have hF0 : s0.reg rgF = gGo := by simp [s0]
  obtain ⟨s', m', hm', hle', hsU', hsG', _⟩ :=
    gcdScaleLoop main k us bU [] s0 (by simpa [s0] using hU) (by simpa [s0] using hG') hF0
  obtain ⟨n, hn, hnle⟩ := Ev.seq e0 ⟨m', hm', le_rfl⟩
  have hsub : cmdTouches gcdScale ⊆ ({sU, sG} : Finset Stk) := by decide
  refine ⟨s', n, hn, by omega, hsU', ?_, ?_⟩
  · simpa using hsG'
  · intro j hjU hjG
    refine Eval.stk_frame hn ?_
    intro hmem
    exact (by simp [Finset.mem_insert, Finset.mem_singleton, hjU, hjG] : j ∉ ({sU, sG} : Finset Stk))
      (hsub hmem)

end Work.IntLib.SqrtGcd
