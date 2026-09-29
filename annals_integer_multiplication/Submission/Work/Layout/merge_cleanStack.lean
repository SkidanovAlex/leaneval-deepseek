import Mathlib
import Submission.Work.Layout.MergeDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# `Work.Layout.merge_cleanStack`

`Work.Layout.Sk.cleanStack SA` removes the cached key sizes from the stack `SA`, down to and
including the boundary marker `gMark` that separates the cache from the data below it.

Statement: if `SA` holds the encodings of the values `CL` (the cache, current front on top) above
the boundary marker `gMark` followed by the glyph list `Sc`, then `cleanStack SA` runs in
`≤ 5 * (encs CL).length + 12` primitive steps, leaves `Sc` on `SA` and leaves every other stack
exactly as it was.

Structure of the proof (`cs`-prefixed helpers; they are named so that this file can be imported
together with the `Layout` development in `Submission/Work/Layout/MergeSteps.lean`):

* `csCleanStack_eq` : `cleanStack SA` is `set rF cons ; loop rF cons (csBody SA)`;
* `csBody_ne` : one non-final iteration — the top of `SA` is a cache entry `h ≠ gMark`, which is
  popped and the loop is continued (`set rF cons`); costs `4` steps;
* `csBody_mark` : the final iteration — the top of `SA` is the boundary marker `gMark`, which is
  popped and the loop is stopped (`set rF gMark`); costs `4` steps;
* `csLoop` : `|CL|` iterations of the first kind followed by one of the second, at `5` steps each
  (`4` for the body plus `1` for the successful loop test);
* the total is `1` (the `set rF cons`) `+ 5 * (|CL| + 1)` (the loop) `+ 1` (the failing loop test)
  `= 5 * |CL| + 7 ≤ 5 * |CL| + 12`.
-/

namespace Work.Layout

open HvdH

/-! ## the loop body of `cleanStack` and its two one-step lemmas -/

/-- body of the `cleanStack` loop: peek the top cell of `SA`; if it is the boundary marker, pop it
and stop (`rF := gMark`), otherwise pop it and continue (`rF := cons`) -/
def csBody (SA : Stk) : Cmd :=
  .seq (.peek SA Sk.rH)
    (.ite Sk.rH gMark (.seq (.pop SA Sk.rJ) (.set Sk.rF gMark))
      (.seq (.pop SA Sk.rJ) (.set Sk.rF Glyph.cons)))

theorem csCleanStack_eq (SA : Stk) :
    Sk.cleanStack SA = .seq (.set Sk.rF Glyph.cons) (.loop Sk.rF Glyph.cons (csBody SA)) := rfl

theorem csBody_ne {main : Cmd} {SA : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {G : List Glyph} (hh : h ≠ gMark) (hX : X SA = h :: G) :
    ∃ s' n, Ev main (csBody SA) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧ s'.stk SA = G ∧
      s'.reg Sk.rF = Glyph.cons ∧ (∀ k' : Stk, k' ≠ SA → s'.stk k' = X k') := by
  have e1 : Ev main (.peek SA Sk.rH) ⟨g, X⟩ ⟨Function.update g Sk.rH h, X⟩ 1 := by
    simpa [hX] using ev_peek' main SA Sk.rH g X
  have hne : (Function.update g Sk.rH h) Sk.rH ≠ gMark := by
    simp only [Function.update_self]; exact hh
  have hp1 : Ev main (.pop SA Sk.rJ) ⟨Function.update g Sk.rH h, X⟩
      ⟨Function.update (Function.update g Sk.rH h) Sk.rJ h, Function.update X SA G⟩ 1 := by
    simpa [hX] using ev_pop' main SA Sk.rJ (Function.update g Sk.rH h) X
  have hp2 : Ev main (.set Sk.rF Glyph.cons)
      ⟨Function.update (Function.update g Sk.rH h) Sk.rJ h, Function.update X SA G⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH h) Sk.rJ h) Sk.rF Glyph.cons,
        Function.update X SA G⟩ 1 :=
    ev_set' main Sk.rF Glyph.cons _ _
  have e2 : Ev main (.ite Sk.rH gMark (.seq (.pop SA Sk.rJ) (.set Sk.rF gMark))
      (.seq (.pop SA Sk.rJ) (.set Sk.rF Glyph.cons)))
      ⟨Function.update g Sk.rH h, X⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH h) Sk.rJ h) Sk.rF Glyph.cons,
        Function.update X SA G⟩ 3 :=
    Ev.iteF hne (Ev.seq' (C := 2) hp1 hp2 (by omega))
  have eall : Ev main (csBody SA) ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH h) Sk.rJ h) Sk.rF Glyph.cons,
        Function.update X SA G⟩ 4 := by
    unfold csBody
    exact Ev.seq' (C := 4) e1 e2 (by omega)
  refine ⟨_, 4, eall, le_rfl, ?_, ?_, ?_⟩
  · simp only [Function.update_self]
  · simp only [Function.update_self]
  · intro k' hk
    simp only [Function.update_of_ne hk]

theorem csBody_mark {main : Cmd} {SA : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {G : List Glyph} (hX : X SA = gMark :: G) :
    ∃ s' n, Ev main (csBody SA) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧ s'.stk SA = G ∧
      s'.reg Sk.rF = gMark ∧ (∀ k' : Stk, k' ≠ SA → s'.stk k' = X k') := by
  have e1 : Ev main (.peek SA Sk.rH) ⟨g, X⟩ ⟨Function.update g Sk.rH gMark, X⟩ 1 := by
    simpa [hX] using ev_peek' main SA Sk.rH g X
  have heq : (Function.update g Sk.rH gMark) Sk.rH = gMark := by simp only [Function.update_self]
  have hp1 : Ev main (.pop SA Sk.rJ) ⟨Function.update g Sk.rH gMark, X⟩
      ⟨Function.update (Function.update g Sk.rH gMark) Sk.rJ gMark, Function.update X SA G⟩ 1 := by
    simpa [hX] using ev_pop' main SA Sk.rJ (Function.update g Sk.rH gMark) X
  have hp2 : Ev main (.set Sk.rF gMark)
      ⟨Function.update (Function.update g Sk.rH gMark) Sk.rJ gMark, Function.update X SA G⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH gMark) Sk.rJ gMark) Sk.rF gMark,
        Function.update X SA G⟩ 1 :=
    ev_set' main Sk.rF gMark _ _
  have e2 : Ev main (.ite Sk.rH gMark (.seq (.pop SA Sk.rJ) (.set Sk.rF gMark))
      (.seq (.pop SA Sk.rJ) (.set Sk.rF Glyph.cons)))
      ⟨Function.update g Sk.rH gMark, X⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH gMark) Sk.rJ gMark) Sk.rF gMark,
        Function.update X SA G⟩ 3 :=
    Ev.iteT heq (Ev.seq' (C := 2) hp1 hp2 (by omega))
  have eall : Ev main (csBody SA) ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g Sk.rH gMark) Sk.rJ gMark) Sk.rF gMark,
        Function.update X SA G⟩ 4 := by
    unfold csBody
    exact Ev.seq' (C := 4) e1 e2 (by omega)
  refine ⟨_, 4, eall, le_rfl, ?_, ?_, ?_⟩
  · simp only [Function.update_self]
  · simp only [Function.update_self]
  · intro k' hk
    simp only [Function.update_of_ne hk]

/-! ## the loop -/

/-- `cleanStack`'s loop runs once per cached value of `Gc` (a list of glyphs containing no `gMark`),
and then once more to consume the boundary marker itself: `|Gc| + 1` iterations, `5` steps each -/
theorem csLoop {main : Cmd} {SA : Stk} :
    ∀ (Gc : List Glyph) (Sc : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ Gc → g Sk.rF = Glyph.cons → X SA = Gc ++ gMark :: Sc →
      ∃ s', loopRuns main Sk.rF Glyph.cons (csBody SA) (Gc.length + 1) ⟨g, X⟩ s'
          (5 * (Gc.length + 1)) ∧
        s'.stk SA = Sc ∧ s'.reg Sk.rF = gMark ∧ (∀ k', k' ≠ SA → s'.stk k' = X k') := by
  intro Gc
  induction Gc with
  | nil =>
      intro Sc g X _ hg hX
      have hX' : X SA = gMark :: Sc := by simpa using hX
      obtain ⟨s', n, he, hn, hSA, hrF, hfr⟩ := csBody_mark (main := main) hX'
      exact ⟨s', loopRuns.one hg (he.mono hn), hSA, hrF, hfr⟩
  | cons h t ih =>
      intro Sc g X hmem hg hX
      have hh : h ≠ gMark := fun e => hmem (e ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ t := fun e => hmem (List.mem_cons_of_mem h e)
      have hX' : X SA = h :: (t ++ gMark :: Sc) := by rw [hX]; rfl
      obtain ⟨s₁, n₁, he₁, hn₁, hSA₁, hrF₁, hfr₁⟩ := csBody_ne (main := main) hh hX'
      obtain ⟨s₂, hrun₂, hSA₂, hrF₂, hfr₂⟩ := ih Sc s₁.reg s₁.stk hmem' hrF₁ hSA₁
      have hcat := loopRuns.concat (t.length + 1) (loopRuns.one hg (he₁.mono hn₁)) hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, hSA₂, hrF₂, ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · intro k' hk; rw [hfr₂ k' hk, hfr₁ k' hk]

/-! ## the assembled statement -/

theorem merge_cleanStack {main : Cmd} {SA : Stk} {CL : List Val} {Sc : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} (h : X SA = encs CL ++ gMark :: Sc) : ∃ s' n, Ev main (Sk.cleanStack SA) ⟨g, X⟩ s' n ∧ n ≤ 5 * (encs CL).length + 12 ∧ s'.stk SA = Sc ∧ (∀ k' : Stk, k' ≠ SA → s'.stk k' = X k') := by
  have hset : Ev main (.set Sk.rF Glyph.cons) ⟨g, X⟩
      ⟨Function.update g Sk.rF Glyph.cons, X⟩ 1 :=
    ev_set' main Sk.rF Glyph.cons g X
  obtain ⟨s₁, hrun, hSA₁, hrF₁, hfr₁⟩ :=
    csLoop (main := main) (SA := SA) (encs CL) Sc (Function.update g Sk.rF Glyph.cons) X
      gMark_not_mem_encs_mg (by simp only [Function.update_self]) (by simpa using h)
  have hne : s₁.reg Sk.rF ≠ Glyph.cons := by rw [hrF₁]; decide
  have hloop : Ev main (.loop Sk.rF Glyph.cons (csBody SA))
      ⟨Function.update g Sk.rF Glyph.cons, X⟩ s₁ (5 * (encs CL).length + 6) :=
    (loopRuns.eval hrun hne).mono (by omega)
  have hmain : Ev main (Sk.cleanStack SA) ⟨g, X⟩ s₁ (1 + (5 * (encs CL).length + 6)) := by
    rw [csCleanStack_eq]
    exact Ev.seq' (C := 1 + (5 * (encs CL).length + 6)) hset hloop (by omega)
  obtain ⟨n, hE, hn⟩ := hmain
  exact ⟨s₁, n, ⟨n, hE, le_rfl⟩, by omega, hSA₁, hfr₁⟩

end Work.Layout
