import Mathlib
import Submission.Work.IntLib.UR.Defs

/-!
# `phase1_eval`: effect and cost of `urPhase1Loop`

`urPhase1Loop c tr` moves every token of the unary counter on stack `c` (down to the counter's own
`gEnd` marker) onto stack `tr`, one token per iteration of its body, and stops as soon as the marker
shows up in the loop register `rD`.  This file proves the specification used by `urDouble`:

* `phase1_body_aux` — one iteration of the body (cost 3) moves exactly one token from `c` to `tr`
  and leaves `rD` holding the head of the remaining counter;
* `phase1_aux` — running the body exactly `v` times (cost `≤ 4v`) empties the counter on `c`
  (leaving `Unary 0 Gc` there), adds its `v` tokens to the counter on `tr`, leaves every other stack
  untouched and stops with `rD = gEnd`;
* `phase1_eval` — the loop itself, cost `≤ 4v + 2`, with the same effect.
-/

set_option autoImplicit false

namespace Work.IntLib.UR

open HvdH
open Work.Layout

/-! ## Reading a unary counter -/

/-- `Unary (n+1) rest` is a token sitting on top of the counter of value `n`. -/
theorem Unary_cons (n : ℕ) (rest : List HvdH.Glyph) : Unary (n + 1) rest = gTok :: Unary n rest := by
  simp only [Unary, List.replicate_succ, List.cons_append]

/-- The tail of the counter of value `n+1`. -/
theorem Unary_tail_cons (n : ℕ) (rest : List HvdH.Glyph) :
    (Unary (n + 1) rest).tail = Unary n rest := by
  simp only [Unary_cons, List.tail_cons]

/-- The head of a non-empty counter is a token. -/
theorem Unary_headD_succ (n : ℕ) (rest : List HvdH.Glyph) (d : HvdH.Glyph) :
    (Unary (n + 1) rest).headD d = gTok := by
  simp only [Unary_cons, List.headD_cons]

/-- The head of the empty counter is the sentinel `gEnd`. -/
theorem Unary_headD_zero' (rest : List HvdH.Glyph) (d : HvdH.Glyph) :
    (Unary 0 rest).headD d = gEnd := by
  simp only [Unary_zero, List.headD_cons]

/-! ## One iteration of the loop -/

/-- One iteration of `urPhase1Loop`: from a state whose stack `c` holds `Unary (v+1) Gc` and whose
stack `tr` holds `Unary j Tr`, the body pops one token off `c`, pushes it on `tr` and peeks the
next token into `rD`; it costs 3 steps. -/
theorem phase1_body_aux (main : HvdH.Cmd) (c tr : HvdH.Stk) (hct : c ≠ tr) (v j : ℕ)
    (Gc Tr : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph)
    (hYc : Y c = Unary (Nat.succ v) Gc) (hYtr : Y tr = Unary j Tr) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph) (Y' : HvdH.Stk → List HvdH.Glyph),
      Ev main (urPhase1Body c tr) ⟨g, Y⟩ ⟨g', Y'⟩ 3 ∧
      Y' c = Unary v Gc ∧ Y' tr = Unary (Nat.succ j) Tr ∧
      g' rD = (Unary v Gc).headD Glyph.eos ∧
      (∀ k : HvdH.Stk, k ≠ c → k ≠ tr → Y' k = Y k) := by
  let g₁ : HvdH.Reg → HvdH.Glyph := Function.update g rD ((Y c).headD Glyph.eos)
  let Y₁ : HvdH.Stk → List HvdH.Glyph := Function.update Y c (Y c).tail
  let Y₂ : HvdH.Stk → List HvdH.Glyph := Function.update Y₁ tr (g₁ rD :: Y₁ tr)
  let g₃ : HvdH.Reg → HvdH.Glyph := Function.update g₁ rD ((Y₂ c).headD Glyph.eos)
  have hY₁c : Y₁ c = Unary v Gc := by
    show Function.update Y c (Y c).tail c = Unary v Gc
    rw [Function.update_self]
    rw [hYc]
    exact Unary_tail_cons v Gc
  have hY₁tr : Y₁ tr = Unary j Tr := by
    show Function.update Y c (Y c).tail tr = Unary j Tr
    rw [Function.update_of_ne (Ne.symm hct)]
    exact hYtr
  have hg₁ : g₁ rD = gTok := by
    show Function.update g rD ((Y c).headD Glyph.eos) rD = gTok
    rw [Function.update_self]
    rw [hYc]
    exact Unary_headD_succ v Gc Glyph.eos
  have hY₂c : Y₂ c = Unary v Gc := by
    show Function.update Y₁ tr (g₁ rD :: Y₁ tr) c = Unary v Gc
    rw [Function.update_of_ne hct]
    exact hY₁c
  have hY₂tr : Y₂ tr = Unary (Nat.succ j) Tr := by
    show Function.update Y₁ tr (g₁ rD :: Y₁ tr) tr = Unary (Nat.succ j) Tr
    rw [Function.update_self]
    rw [hg₁]
    rw [hY₁tr]
    exact (Unary_cons j Tr).symm
  have hg₃ : g₃ rD = (Unary v Gc).headD Glyph.eos := by
    show Function.update g₁ rD ((Y₂ c).headD Glyph.eos) rD = (Unary v Gc).headD Glyph.eos
    rw [Function.update_self]
    rw [hY₂c]
  have hframe : ∀ k : HvdH.Stk, k ≠ c → k ≠ tr → Y₂ k = Y k := by
    intro k hkc hktr
    show Function.update Y₁ tr (g₁ rD :: Y₁ tr) k = Y k
    rw [Function.update_of_ne hktr]
    show Function.update Y c (Y c).tail k = Y k
    rw [Function.update_of_ne hkc]
  have e₁ : Ev main (.pop c rD) ⟨g, Y⟩ ⟨g₁, Y₁⟩ 1 := ev_pop' main c rD g Y
  have e₂ : Ev main (.push tr rD) ⟨g₁, Y₁⟩ ⟨g₁, Y₂⟩ 1 := ev_push' main tr rD g₁ Y₁
  have e₃ : Ev main (.peek c rD) ⟨g₁, Y₂⟩ ⟨g₃, Y₂⟩ 1 := ev_peek' main c rD g₁ Y₂
  exact ⟨g₃, Y₂, Ev.seq e₁ (Ev.seq e₂ e₃), hY₂c, hY₂tr, hg₃, hframe⟩

/-! ## Running the loop -/

/-- Running the body of `urPhase1Loop` `v` times moves the whole counter on `c` onto `tr`, at cost
`≤ 4v`, and stops (leaving `gEnd` in the loop register). -/
theorem phase1_aux (main : HvdH.Cmd) (c tr : HvdH.Stk) (hct : c ≠ tr) :
    ∀ (v j : ℕ) (Gc Tr : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (Y : HvdH.Stk → List HvdH.Glyph),
      Y c = Unary v Gc → Y tr = Unary j Tr → g rD = (Unary v Gc).headD Glyph.eos →
      ∃ (g' : HvdH.Reg → HvdH.Glyph) (Y' : HvdH.Stk → List HvdH.Glyph),
        loopRuns main rD gTok (urPhase1Body c tr) v ⟨g, Y⟩ ⟨g', Y'⟩ (4 * v) ∧
        g' rD = gEnd ∧ Y' c = Unary 0 Gc ∧ Y' tr = Unary (j + v) Tr ∧
        (∀ k : HvdH.Stk, k ≠ c → k ≠ tr → Y' k = Y k) := by
  intro v
  induction v with
  | zero =>
      intro j Gc Tr g Y hYc hYtr hgr
      refine ⟨g, Y, ?_, ?_, hYc, ?_, ?_⟩
      · have h0 : loopRuns main rD gTok (urPhase1Body c tr) 0 ⟨g, Y⟩ ⟨g, Y⟩ 0 := loopRuns.zero
        simpa using h0
      · rw [hgr]
        exact Unary_headD_zero' Gc Glyph.eos
      · simpa using hYtr
      · intro k _ _; rfl
  | succ v ih =>
      intro j Gc Tr g Y hYc hYtr hgr
      obtain ⟨g₁, Y₁, hbody, hY₁c, hY₁tr, hg₁, hframe₁⟩ :=
        phase1_body_aux main c tr hct v j Gc Tr g Y hYc hYtr
      obtain ⟨g', Y', hloop, hg', hY'c, hY'tr, hframe'⟩ :=
        ih (Nat.succ j) Gc Tr g₁ Y₁ hY₁c hY₁tr hg₁
      have hgr' : g rD = gTok := by
        rw [hgr]
        exact Unary_headD_succ v Gc Glyph.eos
      have hassoc : Nat.succ j + v = j + Nat.succ v := by omega
      refine ⟨g', Y', ?_, hg', hY'c, ?_, ?_⟩
      · exact loopRuns.succ' hgr' hbody hloop (by omega)
      · rw [hY'tr, hassoc]
      · intro k hkc hktr
        rw [hframe' k hkc hktr, hframe₁ k hkc hktr]

theorem phase1_eval (main : HvdH.Cmd) (c tr : HvdH.Stk) (hct : c ≠ tr) (v j : ℕ)
    (Gc Tr : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (hc : X c = Work.IntLib.Unary v Gc) (htr : X tr = Work.IntLib.Unary j Tr)
    (hr : g Work.IntLib.UR.rD = (Work.IntLib.Unary v Gc).headD HvdH.Glyph.eos) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph) (X' : HvdH.Stk → List HvdH.Glyph) (n : ℕ),
      Work.Layout.Ev main (Work.IntLib.UR.urPhase1Loop c tr) ⟨g, X⟩ ⟨g', X'⟩ n ∧ n ≤ 4 * v + 2 ∧
      X' c = Work.IntLib.Unary 0 Gc ∧ X' tr = Work.IntLib.Unary (j + v) Tr ∧
      (∀ k : HvdH.Stk, k ≠ c → k ≠ tr → X' k = X k) := by
  obtain ⟨g', X', hloop, hg', hX'c, hX'tr, hframe⟩ :=
    phase1_aux main c tr hct v j Gc Tr g X hc htr hr
  have hne : g' rD ≠ gTok := by
    rw [hg']
    exact gEnd_ne_gTok
  exact ⟨g', X', 4 * v + 1, loopRuns.eval hloop hne, by omega, hX'c, hX'tr, hframe⟩

end Work.IntLib.UR
