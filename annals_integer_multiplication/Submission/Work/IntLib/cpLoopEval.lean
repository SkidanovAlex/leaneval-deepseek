import Mathlib
import Submission.Work.IntLib.cpDefs

/-!
# IntLib: evaluation and cost of the copy loop `cpLoop`

`Work.IntLib.cpLoop a b c` is the loop `.loop rD gTok (cpBody a b c)` whose body
`cpBody a b c = pop a rD ; push c rD ; push b rD ; peek a rD` moves one token of the unary
counter sitting on stack `a` onto both `b` and `c`, one iteration per token.  After `v` iterations:

* `a` is emptied down to its own sentinel (`Unary 0 Ga`),
* `b` (= `B` before) and `c` (= `C` before) each receive `v` copies of `gTok`,
* the loop register `rD` holds `gEnd`, so the loop stops,
* cost: `4` per iteration plus one `loop` test per iteration and one final failed test, i.e. `5v+1`.

The main statement below, `cpLoopEval`, is exactly the interface used by `unaryCopyV2`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Small facts about unary counters -/

theorem cp_Unary_tail (n : ℕ) (rest : List Glyph) : (Unary (n + 1) rest).tail = Unary n rest := by
  rw [Unary_succ]; rfl

theorem cp_Unary_headD_succ (n : ℕ) (rest : List Glyph) (d : Glyph) :
    (Unary (n + 1) rest).headD d = gTok := by rw [Unary_succ]; rfl

theorem cp_Unary_headD_zero (rest : List Glyph) (d : Glyph) : (Unary 0 rest).headD d = gEnd := by
  rw [Unary_zero]; rfl

theorem cp_replicate_succ_append (v : ℕ) (B : List Glyph) :
    List.replicate v gTok ++ (gTok :: B) = List.replicate (v + 1) gTok ++ B := by
  rw [List.replicate_succ', List.append_assoc]
  rfl

/-! ## One iteration of the loop -/

/-- One iteration of `cpLoop`: from a state whose stack `a` holds the counter `Unary (v+1) Ga`
and whose loop register holds `gTok`, the body pops one token off `a`, pushes it on `c` and on `b`
and peeks the new head of `a` into `rD`.  It costs `4` steps. -/
theorem cp_body_aux (main : Cmd) (a b c : Stk) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : ℕ) (Ga B C : List Glyph) (g : Reg → Glyph) (Y : Stk → List Glyph)
    (hYa : Y a = Unary (v + 1) Ga) (hYb : Y b = B) (hYc : Y c = C)
    (_hg : g UR.rD = gTok) :
    ∃ (g' : Reg → Glyph) (Y' : Stk → List Glyph),
      Ev main (cpBody a b c) ⟨g, Y⟩ ⟨g', Y'⟩ 4 ∧
      Y' a = Unary v Ga ∧ Y' b = gTok :: B ∧ Y' c = gTok :: C ∧
      g' UR.rD = (Unary v Ga).headD Glyph.eos := by
  let g₁ : Reg → Glyph := Function.update g UR.rD ((Y a).headD Glyph.eos)
  let Y₁ : Stk → List Glyph := Function.update Y a (Y a).tail
  let Y₂ : Stk → List Glyph := Function.update Y₁ c (g₁ UR.rD :: Y₁ c)
  let Y₃ : Stk → List Glyph := Function.update Y₂ b (g₁ UR.rD :: Y₂ b)
  let g₄ : Reg → Glyph := Function.update g₁ UR.rD ((Y₃ a).headD Glyph.eos)
  have hg₁ : g₁ UR.rD = gTok := by
    show Function.update g UR.rD ((Y a).headD Glyph.eos) UR.rD = gTok
    rw [Function.update_self, hYa, cp_Unary_headD_succ]
  have hY₁a : Y₁ a = Unary v Ga := by
    show Function.update Y a (Y a).tail a = Unary v Ga
    rw [Function.update_self, hYa, cp_Unary_tail]
  have hY₁b : Y₁ b = B := by
    show Function.update Y a (Y a).tail b = B
    rw [Function.update_of_ne hab.symm, hYb]
  have hY₁c : Y₁ c = C := by
    show Function.update Y a (Y a).tail c = C
    rw [Function.update_of_ne hac.symm, hYc]
  have hY₂a : Y₂ a = Unary v Ga := by
    show Function.update Y₁ c (g₁ UR.rD :: Y₁ c) a = Unary v Ga
    rw [Function.update_of_ne hac, hY₁a]
  have hY₂b : Y₂ b = B := by
    show Function.update Y₁ c (g₁ UR.rD :: Y₁ c) b = B
    rw [Function.update_of_ne hbc, hY₁b]
  have hY₂c : Y₂ c = gTok :: C := by
    show Function.update Y₁ c (g₁ UR.rD :: Y₁ c) c = gTok :: C
    rw [Function.update_self, hg₁, hY₁c]
  have hY₃a : Y₃ a = Unary v Ga := by
    show Function.update Y₂ b (g₁ UR.rD :: Y₂ b) a = Unary v Ga
    rw [Function.update_of_ne hab, hY₂a]
  have hY₃b : Y₃ b = gTok :: B := by
    show Function.update Y₂ b (g₁ UR.rD :: Y₂ b) b = gTok :: B
    rw [Function.update_self, hg₁, hY₂b]
  have hY₃c : Y₃ c = gTok :: C := by
    show Function.update Y₂ b (g₁ UR.rD :: Y₂ b) c = gTok :: C
    rw [Function.update_of_ne hbc.symm, hY₂c]
  have hg₄ : g₄ UR.rD = (Unary v Ga).headD Glyph.eos := by
    show Function.update g₁ UR.rD ((Y₃ a).headD Glyph.eos) UR.rD = (Unary v Ga).headD Glyph.eos
    rw [Function.update_self, hY₃a]
  have e₁ : Ev main (.pop a UR.rD) ⟨g, Y⟩ ⟨g₁, Y₁⟩ 1 := ev_pop' main a UR.rD g Y
  have e₂ : Ev main (.push c UR.rD) ⟨g₁, Y₁⟩ ⟨g₁, Y₂⟩ 1 := ev_push' main c UR.rD g₁ Y₁
  have e₃ : Ev main (.push b UR.rD) ⟨g₁, Y₂⟩ ⟨g₁, Y₃⟩ 1 := ev_push' main b UR.rD g₁ Y₂
  have e₄ : Ev main (.peek a UR.rD) ⟨g₁, Y₃⟩ ⟨g₄, Y₃⟩ 1 := ev_peek' main a UR.rD g₁ Y₃
  exact ⟨g₄, Y₃, Ev.seq e₁ (Ev.seq e₂ (Ev.seq e₃ e₄)), hY₃a, hY₃b, hY₃c, hg₄⟩

/-! ## The whole loop -/

/-- Running `cpBody a b c` exactly `v` times moves the `v` tokens of the counter on `a` onto both
`b` and `c`, at cost `≤ 5v` (body cost `4` plus one successful test per iteration), and leaves
`gEnd` in the loop register. -/
theorem cp_aux (main : Cmd) (a b c : Stk) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (v : ℕ) (Ga B C : List Glyph) (g : Reg → Glyph) (Y : Stk → List Glyph),
      Y a = Unary v Ga → Y b = B → Y c = C → g UR.rD = (Unary v Ga).headD Glyph.eos →
      ∃ (g' : Reg → Glyph) (Y' : Stk → List Glyph),
        loopRuns main UR.rD gTok (cpBody a b c) v ⟨g, Y⟩ ⟨g', Y'⟩ (5 * v) ∧
        g' UR.rD = gEnd ∧ Y' a = Unary 0 Ga ∧
        Y' b = List.replicate v gTok ++ B ∧ Y' c = List.replicate v gTok ++ C := by
  intro v
  induction v with
  | zero =>
      intro Ga B C g Y hYa hYb hYc hg
      refine ⟨g, Y, loopRuns.zero, ?_, hYa, ?_, ?_⟩
      · rw [hg]; exact cp_Unary_headD_zero Ga Glyph.eos
      · simpa using hYb
      · simpa using hYc
  | succ v ih =>
      intro Ga B C g Y hYa hYb hYc hg
      have hgTok : g UR.rD = gTok := by
        rw [hg]; exact cp_Unary_headD_succ v Ga Glyph.eos
      obtain ⟨g₁, Y₁, hbody, hY₁a, hY₁b, hY₁c, hg₁⟩ :=
        cp_body_aux main a b c hab hac hbc v Ga B C g Y hYa hYb hYc hgTok
      obtain ⟨g', Y', hloop, hg', hY'a, hY'b, hY'c⟩ :=
        ih Ga (gTok :: B) (gTok :: C) g₁ Y₁ hY₁a hY₁b hY₁c hg₁
      have hrep : List.replicate v gTok ++ (gTok :: B) = List.replicate (v + 1) gTok ++ B :=
        cp_replicate_succ_append v B
      have hrepC : List.replicate v gTok ++ (gTok :: C) = List.replicate (v + 1) gTok ++ C :=
        cp_replicate_succ_append v C
      refine ⟨g', Y', ?_, hg', hY'a, ?_, ?_⟩
      · exact loopRuns.succ' hgTok hbody hloop (by omega)
      · rw [hY'b]; exact hrep
      · rw [hY'c]; exact hrepC

/-! ## The loop as a program -/

theorem cpLoopEval (main : HvdH.Cmd) (a b c : HvdH.Stk)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (v : ℕ) (Ga B C : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (Y : HvdH.Stk → List HvdH.Glyph),
      Y a = Work.IntLib.Unary v Ga → Y b = B → Y c = C →
      g Work.IntLib.UR.rD = (Work.IntLib.Unary v Ga).headD HvdH.Glyph.eos →
      ∃ (g' : HvdH.Reg → HvdH.Glyph) (Y' : HvdH.Stk → List HvdH.Glyph) (n : ℕ),
        Work.Layout.Ev main (Work.IntLib.cpLoop a b c) ⟨g, Y⟩ ⟨g', Y'⟩ n ∧ n ≤ 5 * v + 1 ∧
        Y' a = Work.IntLib.Unary 0 Ga ∧
        Y' b = List.replicate v Work.IntLib.gTok ++ B ∧
        Y' c = List.replicate v Work.IntLib.gTok ++ C ∧
        (∀ k : HvdH.Stk, k ≠ a → k ≠ b → k ≠ c → Y' k = Y k) := by
  intro v Ga B C g Y hYa hYb hYc hg
  obtain ⟨g', Y', hloop, hg', hY'a, hY'b, hY'c⟩ :=
    cp_aux main a b c hab hac hbc v Ga B C g Y hYa hYb hYc hg
  have hne : g' UR.rD ≠ gTok := by rw [hg']; exact gEnd_ne_gTok
  obtain ⟨n₀, hev, hle₀⟩ := loopRuns.eval hloop hne
  have hEv : Ev main (cpLoop a b c) ⟨g, Y⟩ ⟨g', Y'⟩ (5 * v + 1) := ⟨n₀, hev, hle₀⟩
  refine ⟨g', Y', 5 * v + 1, hEv, le_rfl, hY'a, hY'b, hY'c, ?_⟩
  intro k hka hkb hkc
  exact Eval.stk_frame hev (by simp [cmdTouches, cpBody, hka, hkb, hkc])

end Work.IntLib
