import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.prependTo_ev
import Submission.Work.SynFFT.prependToScratchEv
import Submission.Work.Kernel.Raw

/-!
# `zipCatWord`: definitions, size facts and the two gadgets

This module prepares the proof of `Work.SynFFT.zipCatWord`: the StackLang word that merges two
groups of rows elementwise (`Work.SynFFT.zipCat`) at cost `O(vsz G₁ + vsz G₂)`.

Stacks used by the word:

* `0` — the value stack (frame `encs rest ++ R` while the loop runs, the result at the end);
* `1` — the remaining rows of the first group, as the *value* `ofList (A₁.map ofList)`;
* `2` — the remaining rows of the second group, likewise;
* `3` — the accumulator: the reversed list of already-merged rows, as a value;
* `4`, `5` — scratch for `Work.Layout.mvVal` / `Work.Layout.prependTo` (always restored).

Registers `0`–`4` are clobbered by the value movers, so the loop flag lives in register `zF = 5`
and the `peek` register is `zP = 6`.

## Contents

* `vsz` facts for `ofList` / `grpVal` / `zipCat`;
* `zBump` / `zCost` / `zStepCost`: the cost accounting functions of the loop, with the exact
  telescoping identity `zCost A₁ A₂ = zStepCost A₁ A₂ + zCost (A₁.tailD []) (A₂.tailD [])`;
* `unconsTo_ev_full`: `Work.Layout.unconsTo` with *all* scratch stacks restored;
* `zMer` / `zMer_ev`: the "merge, prepend to the accumulator, continue" gadget
  (`zApp` = `Work.Layout.appendWord`, `Work.Layout.prependTo`, `.set zF Glyph.cons`);
* `zBody` / `zProg`: the loop body and the loop of the word.

The per-iteration case analysis (`zStep_*`) is proved in separate modules
(`Submission/Work/SynFFT/zipStep*.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH
open Work.Layout

/-! ## 1. Registers -/

/-- loop flag register of the `zipCat` word (outside `{0,1,2,3,4}`, which the movers clobber) -/
def zF : Reg := 5

/-- register receiving the glyph read by `peek` in the loop body -/
def zP : Reg := 6

/-! ## 2. Sizes -/

theorem vsz_cons (x y : Val) : vsz (Val.cons x y) = vsz x + vsz y + 1 := by
  simp [vsz, Val.enc, List.length_append]

/-- size of a list value -/
theorem vsz_ofList_sum (l : List Val) : vsz (ofList l) = (l.map (fun v => vsz v + 1)).sum + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl, vsz_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem vsz_ofList_append (l₁ l₂ : List Val) :
    vsz (ofList (l₁ ++ l₂)) + 1 = vsz (ofList l₁) + vsz (ofList l₂) := by
  rw [vsz_ofList_sum, vsz_ofList_sum, vsz_ofList_sum, List.map_append, List.sum_append]
  ring

theorem vsz_ofList_reverse (l : List Val) : vsz (ofList l.reverse) = vsz (ofList l) := by
  rw [vsz_ofList_sum, vsz_ofList_sum, List.map_reverse, List.sum_reverse]

/-- size of a group value -/
theorem vsz_grpVal (G : List (List Val)) :
    vsz (grpVal G) = (G.map (fun r => vsz (ofList r) + 1)).sum + 1 := by
  rw [grpVal, vsz_ofList_sum, List.map_map]
  rfl

theorem vsz_grpVal_nil : vsz (grpVal ([] : List (List Val))) = 1 := rfl

theorem vsz_grpVal_cons (r : List Val) (t : List (List Val)) :
    vsz (grpVal (r :: t)) = vsz (ofList r) + 1 + vsz (grpVal t) := by
  rw [vsz_grpVal, vsz_grpVal]
  simp only [List.map_cons, List.sum_cons]
  omega

theorem vsz_grpVal_reverse (G : List (List Val)) : vsz (grpVal G.reverse) = vsz (grpVal G) := by
  rw [vsz_grpVal, vsz_grpVal, List.map_reverse, List.sum_reverse]

/-- merging is size-subadditive -/
theorem vsz_grpVal_le_zipCat (A B : List (List Val)) :
    vsz (grpVal (zipCat A B)) ≤ vsz (grpVal A) + vsz (grpVal B) := by
  induction A generalizing B with
  | nil => simp
  | cons r t ih =>
      cases B with
      | nil => simp
      | cons s u =>
          rw [show zipCat (r :: t) (s :: u) = (r ++ s) :: zipCat t u from rfl,
            vsz_grpVal_cons, vsz_grpVal_cons, vsz_grpVal_cons, vsz_ofList_append]
          have := ih u
          omega

/-! ## 3. The cost functions of the loop -/

/-- size contributed by the head row of a group (0 for the empty group) -/
def zBump (A : List (List Val)) : ℕ := if A = [] then 0 else vsz (ofList (A.headD [])) + 1

theorem zBump_nil : zBump ([] : List (List Val)) = 0 := by simp [zBump]

theorem zBump_cons (r : List Val) (t : List (List Val)) : zBump (r :: t) = vsz (ofList r) + 1 := by
  simp [zBump]

/-- the size of a group splits into its head row and its tail -/
theorem vsz_grpVal_eq_zBump (A : List (List Val)) :
    vsz (grpVal A) = zBump A + vsz (grpVal (A.tailD [])) := by
  cases A with
  | nil => simp [zBump, vsz_grpVal_nil]
  | cons r t => rw [zBump_cons, vsz_grpVal_cons]; simp

theorem zBump_le (A : List (List Val)) : zBump A ≤ vsz (grpVal A) := by
  cases A with
  | nil => simp [zBump]
  | cons r t => rw [zBump_cons, vsz_grpVal_cons]; omega

/-- total cost budget of the loop for the remaining groups `A₁`, `A₂` -/
def zCost (KA : ℕ) (A₁ A₂ : List (List Val)) : ℕ :=
  (KA + 100) * (vsz (grpVal A₁) + vsz (grpVal A₂) + 1)

/-- budget of one loop iteration (one row of each group is consumed) -/
def zStepCost (KA : ℕ) (A₁ A₂ : List (List Val)) : ℕ := (KA + 100) * (zBump A₁ + zBump A₂)

/-- exact telescoping of the loop budget -/
theorem zCost_tail (KA : ℕ) (A₁ A₂ : List (List Val)) :
    zCost KA A₁ A₂ = zStepCost KA A₁ A₂ + zCost KA (A₁.tailD []) (A₂.tailD []) := by
  rw [zCost, zStepCost, zCost, vsz_grpVal_eq_zBump A₁, vsz_grpVal_eq_zBump A₂]
  ring

/-- `zipCat` splits along the heads -/
theorem zipCat_headD (A B : List (List Val)) (h : A ≠ [] ∨ B ≠ []) :
    zipCat A B = (A.headD [] ++ B.headD []) :: zipCat (A.tailD []) (B.tailD []) := by
  rcases A with _ | ⟨r, t⟩ <;> rcases B with _ | ⟨s, u⟩
  · rcases h with h | h <;> exact absurd rfl h
  · simp
  · simp
  · rfl

/-! ## 4. Encodings of cons-cells of group values -/

theorem ofList_map_ofList_cons (r : List Val) (t : List (List Val)) :
    (ofList ((r :: t).map ofList)).enc =
      Glyph.cons :: ((ofList r).enc ++ (ofList (t.map ofList)).enc) := rfl

theorem ofList_map_ofList_nil :
    (ofList (([] : List (List Val)).map ofList)).enc = [Glyph.nil] := rfl

/-! ## 5. `unconsTo` with all scratch stacks restored -/

/-- `Work.Layout.unconsTo a b c d rr` pops the leading `cons` of stack `a` and moves the exposed
value `v` on top of stack `b`, restoring the scratch stacks `c`, `d` (this is
`Work.Layout.AA.unconsTo_ev` with the full-strength mover `Work.Layout.mvVal_ev_full`). -/
theorem unconsTo_ev_full {main : Cmd} {a b c d : Stk} {rr : Reg}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val} {A : List Glyph}
    (ha : X a = Glyph.cons :: (v.enc ++ A)) :
    ∃ s' n, Ev main (unconsTo a b c d rr) ⟨g, X⟩ s' n ∧ n ≤ 20 * (vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ X b ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  have h1 : Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr ((X a).headD Glyph.eos), Function.update X a (X a).tail⟩ 1 :=
    ev_pop' main a rr g X
  have ha' : Function.update X a (X a).tail a = v.enc ++ A := by
    simp only [stkFn_same, ha, tail_cons]
  have hb' : Function.update X a (X a).tail b = X b :=
    stkFn_ne X hab.symm (X a).tail
  obtain ⟨s₂, n₂, h2, hn₂, ha₂, hb₂, hc₂, hd₂, hf₂⟩ :=
    mvVal_ev_full (main := main) hab hac had hbc hbd hcd
      (g := Function.update g rr ((X a).headD Glyph.eos))
      (X := Function.update X a (X a).tail) (v := v) (A := A) (B := X b) ha' hb'
  have hupd : ∀ j, j ≠ a → Function.update X a (X a).tail j = X j :=
    fun j hj => stkFn_ne X hj (X a).tail
  have hmain : Ev main (unconsTo a b c d rr) ⟨g, X⟩ s₂ (n₂ + 1) := by
    unfold unconsTo
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨s₂, _, hmain, by omega, ha₂, hb₂, ?_, ?_, ?_⟩
  · rw [hc₂, hupd c hac.symm]
  · rw [hd₂, hupd d had.symm]
  · intro j hja hjb hjc hjd
    rw [hf₂ j hja hjb hjc hjd, hupd j hja]

/-! ## 6. The merge gadget -/

/-- Merge the two row values on top of the value stack, prepend the merged row to the accumulator
value on stack `3`, and set the loop flag to `cons` (continue). -/
def zMer (zApp : Cmd) (f : Reg) : Cmd := seqs [zApp, prependTo 0 3 4 5 rA, .set f Glyph.cons]

/-- **The merge gadget**: from `ofList r₁ :: ofList r₂ :: rest` on the value stack (frame `R`) and
`ofList (Racc.map ofList)` on stack `3`, produce `rest` (frame `R`) and
`ofList (ofList (r₁ ++ r₂) :: Racc.map ofList)` on stack `3`, at cost
`KA (vsz (ofList r₁) + 1) + 20 (vsz (ofList r₁) + vsz (ofList r₂)) + 6`; stacks `4`, `5` and all
other stacks are restored. -/
theorem zMer_ev {main : Cmd} {zApp : Cmd} {KA : ℕ} {f : Reg}
    (hApp : ∀ (xs ys rest' : List Val), WordR main zApp
      (fun vs => vs = ofList xs :: ofList ys :: rest')
      (fun _ out => out = ofList (xs ++ ys) :: rest')
      (fun _ => KA * (vsz (ofList xs) + 1)))
    {rest : List Val} {R : List Glyph} {r₁ r₂ : List Val} {Racc : List (List Val)}
    {Z3 : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (h0 : X 0 = encs (ofList r₁ :: ofList r₂ :: rest) ++ R)
    (h3 : X 3 = (ofList (Racc.map ofList)).enc ++ Z3) :
    ∃ s' n, Ev main (zMer zApp f) ⟨g, X⟩ s' n ∧
      n ≤ KA * (vsz (ofList r₁) + 1) + 20 * (vsz (ofList r₁) + vsz (ofList r₂)) + 6 ∧
      s'.stk 0 = encs rest ++ R ∧
      s'.stk 3 = (ofList ((ofList (r₁ ++ r₂)) :: Racc.map ofList)).enc ++ Z3 ∧
      s'.reg f = Glyph.cons ∧ s'.stk 4 = X 4 ∧ s'.stk 5 = X 5 ∧
      (∀ k, k ≠ 0 → k ≠ 3 → k ≠ 4 → k ≠ 5 → s'.stk k = X k) := by
  -- step 1: merge the two row values
  obtain ⟨out, s₁, n₁, hout, hEval, hn₁, hstk₁, hoth₁⟩ :=
    hApp r₁ r₂ rest (ofList r₁ :: ofList r₂ :: rest) rfl ⟨g, X⟩ R h0
  have hn₁' : n₁ ≤ KA * (vsz (ofList r₁) + 1) := hn₁
  have hEv₁ : Ev main zApp ⟨g, X⟩ s₁ n₁ := ⟨n₁, hEval, le_rfl⟩
  have hs₁0 : s₁.stk 0 = (ofList (r₁ ++ r₂)).enc ++ (encs rest ++ R) := by
    rw [hstk₁, hout]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  have hs₁3 : s₁.stk 3 = (ofList (Racc.map ofList)).enc ++ Z3 := by
    rw [hoth₁ 3 (by decide)]
    exact h3
  -- step 2: prepend the merged row to the accumulator
  obtain ⟨s₂, n₂, h2, hn₂, hs₂0, hs₂3, hs₂4, hs₂5, hf₂⟩ :=
    prependToScratchEv main 0 3 4 5 rA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s₁.reg s₁.stk (ofList (r₁ ++ r₂)) (Racc.map ofList)
      (encs rest ++ R) Z3 hs₁0 hs₁3
  -- step 3: continue
  have hset : Ev main (.set f Glyph.cons) s₂ ⟨Function.update s₂.reg f Glyph.cons, s₂.stk⟩ 1 :=
    ev_set' main f Glyph.cons s₂.reg s₂.stk
  have hmain : Ev main (zMer zApp f) ⟨g, X⟩ ⟨Function.update s₂.reg f Glyph.cons, s₂.stk⟩
      (n₁ + (n₂ + 1)) := by
    unfold zMer
    simp only [seqs]
    exact Ev.seq' hEv₁ (Ev.seq' h2 hset (le_refl _)) (by omega)
  refine ⟨_, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 := vsz_ofList_append r₁ r₂
    omega
  · exact hs₂0
  · simpa using hs₂3
  · simp
  · rw [hs₂4, hoth₁ 4 (by decide)]
  · rw [hs₂5, hoth₁ 5 (by decide)]
  · intro k hk0 hk3 hk4 hk5
    rw [hf₂ k hk0 hk3, hoth₁ k hk0]

/-! ## 7. The loop body and the loop -/

/-- body of the main loop: while one of the two stacks `1`, `2` still carries a `cons` cell, take
the head rows of the nonempty group(s) (using the empty row when one group is exhausted), merge
them with `zMer`, and continue; stop when both groups are exhausted. -/
def zBody (zApp : Cmd) : Cmd :=
  seqs [ .peek 1 zP,
    .ite zP Glyph.cons
      (seqs [ .pop 1 rA,
        .peek 2 zP,
        .ite zP Glyph.cons
          (seqs [ .pop 2 rA, mvVal 2 0 4 5, mvVal 1 0 4 5, zMer zApp zF ])
          (seqs [ pushConst 0 Glyph.nil, mvVal 1 0 4 5, zMer zApp zF ]) ])
      (seqs [ .peek 2 zP,
        .ite zP Glyph.cons
          (seqs [ pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF ])
          (.set zF Glyph.eos) ]) ]

/-- the main loop of the `zipCat` word -/
def zProg (zApp : Cmd) : Cmd := .loop zF Glyph.cons (zBody zApp)

end Work.SynFFT
