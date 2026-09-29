import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.SqrtGcd.sqrtStepSpec
import Submission.Work.IntLib.SqrtGcd.subLoopEvalXU
import Submission.Work.IntLib.SqrtGcd.subDigitsSpec
import Submission.Work.IntLib.SqrtGcd.subDigitsArith
import Submission.Work.IntLib.SqrtGcd.dup2EvalGen
import Submission.Work.IntLib.SqrtGcd.moveSameSpec
import Submission.Work.Layout.Base

/-!
# Toolkit for the square-root loop `SG.sqrtLoop`

Definitions and generic lemmas used by the correctness proof of `SG.sqrtLoop`
(`sqrtLoopEval.lean`):

* `Frame7` — the seven stacks `1..7` are the only ones the loop may touch;
* `cmdTouchesR` / `Eval.reg_frame` — the register analogue of `Work.Layout.cmdTouches` /
  `Eval.stk_frame` (needed to know that `sqrtWork` leaves the loop flag `rgF` alone);
* `sqrtStep_snd` / `sqrtStep_trd` — unfolding `SG.sqrtStep`;
* `Inv` — the invariant of the loop.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.Layout Work.IntLib
open Work.IntLib.SG

/-! ## The seven-stack frame -/

/-- The frame condition of the square-root loop: all stacks other than `sA … sS` are restored. -/
def Frame7 (s₀ s : State) : Prop :=
  ∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ sC → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
    s.stk j = s₀.stk j

theorem Frame7.refl (s : State) : Frame7 s s := fun _ _ _ _ _ _ _ _ => rfl

theorem Frame7.trans {s t u : State} (h1 : Frame7 s t) (h2 : Frame7 t u) : Frame7 s u :=
  fun j ha hb hc hd he hf hg => (h2 j ha hb hc hd he hf hg).trans (h1 j ha hb hc hd he hf hg)

theorem frame7_of_keepsA {s t : State} (h : ∀ j : Stk, j ≠ sA → t.stk j = s.stk j) :
    Frame7 s t := fun j ha _ _ _ _ _ _ => h j ha

theorem frame7_of_keepsB {s t : State} (h : ∀ j : Stk, j ≠ sB → t.stk j = s.stk j) :
    Frame7 s t := fun j _ hb _ _ _ _ _ => h j hb

theorem frame7_of_keepsC {s t : State} (h : ∀ j : Stk, j ≠ sC → t.stk j = s.stk j) :
    Frame7 s t := fun j _ _ hc _ _ _ _ => h j hc

theorem frame7_of_keepsP {s t : State} (h : ∀ j : Stk, j ≠ sP → t.stk j = s.stk j) :
    Frame7 s t := fun j _ _ _ hd _ _ _ => h j hd

theorem frame7_of_keepsQ {s t : State} (h : ∀ j : Stk, j ≠ sQ → t.stk j = s.stk j) :
    Frame7 s t := fun j _ _ _ _ he _ _ => h j he

theorem frame7_of_keepsR {s t : State} (h : ∀ j : Stk, j ≠ sR → t.stk j = s.stk j) :
    Frame7 s t := fun j _ _ _ _ _ hf _ => h j hf

theorem frame7_of_keepsS {s t : State} (h : ∀ j : Stk, j ≠ sS → t.stk j = s.stk j) :
    Frame7 s t := fun j _ _ _ _ _ _ hg => h j hg

/-- The frame produced by `dup2` (it rewrites `src`, `dst`, `t1`, `t2`). -/
theorem frame7_of_keeps4 {s t : State} {a b c d : Stk}
    (h : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ c → j ≠ d → t.stk j = s.stk j)
    (ha : a = sA ∨ a = sB ∨ a = sC ∨ a = sP ∨ a = sQ ∨ a = sR ∨ a = sS)
    (hb : b = sA ∨ b = sB ∨ b = sC ∨ b = sP ∨ b = sQ ∨ b = sR ∨ b = sS)
    (hc : c = sA ∨ c = sB ∨ c = sC ∨ c = sP ∨ c = sQ ∨ c = sR ∨ c = sS)
    (hd : d = sA ∨ d = sB ∨ d = sC ∨ d = sP ∨ d = sQ ∨ d = sR ∨ d = sS) :
    Frame7 s t := by
  intro j hjA hjB hjC hjP hjQ hjR hjS
  refine h j ?_ ?_ ?_ ?_
  · rcases ha with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hb with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hc with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hd with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption

/-- The frame produced by `subLoop` (it rewrites `sP`, `sR`, `sS`). -/
theorem frame7_of_keeps3 {s t : State}
    (h : ∀ j : Stk, j ≠ sP → j ≠ sR → j ≠ sS → t.stk j = s.stk j) : Frame7 s t :=
  fun j _ _ _ hd _ hf hg => h j hd hf hg

/-! ## Registers a program touches -/

/-- The set of registers a program may write.  Unlike `Work.Layout.cmdTouches` (which records the
*stacks* a program may touch) this records the registers: `push`, `ite`, `loop`, `skip` and the
tests do not change any register. -/
def cmdTouchesR : Cmd → Finset Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov dst _ => {dst}
  | .seq a b => cmdTouchesR a ∪ cmdTouchesR b
  | .ite _ _ a b => cmdTouchesR a ∪ cmdTouchesR b
  | .loop _ _ a => cmdTouchesR a
  | .self => Finset.univ

theorem Eval.reg_frame {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n)
    {r : Reg} (hr : r ∉ cmdTouchesR c) : s'.reg r = s.reg r := by
  induction h with
  | skip s => rfl
  | pop k' r' s =>
      simp only [cmdTouchesR, Finset.mem_singleton] at hr
      show Function.update s.reg r' ((s.stk k').headD .eos) r = s.reg r
      exact Function.update_of_ne hr _ _
  | peek k' r' s =>
      simp only [cmdTouchesR, Finset.mem_singleton] at hr
      show Function.update s.reg r' ((s.stk k').headD .eos) r = s.reg r
      exact Function.update_of_ne hr _ _
  | push k' r' s => rfl
  | set r' c' s =>
      simp only [cmdTouchesR, Finset.mem_singleton] at hr
      show Function.update s.reg r' c' r = s.reg r
      exact Function.update_of_ne hr _ _
  | mov dst src s =>
      simp only [cmdTouchesR, Finset.mem_singleton] at hr
      show Function.update s.reg dst (s.reg src) r = s.reg r
      exact Function.update_of_ne hr _ _
  | seq h₁ h₂ ih₁ ih₂ =>
      simp only [cmdTouchesR, Finset.mem_union, not_or] at hr
      rw [ih₂ hr.2, ih₁ hr.1]
  | iteT hr' h ih =>
      simp only [cmdTouchesR, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | iteF hr' h ih =>
      simp only [cmdTouchesR, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopF hr' => rfl
  | loopT hr' h₁ h₂ ih₁ ih₂ =>
      simp only [cmdTouchesR] at hr
      rw [ih₂ hr, ih₁ hr]
  | self h ih => exact absurd (Finset.mem_univ _) hr

theorem Ev.reg_frame {main : Cmd} {p : Cmd} {s s' : State} {C : ℕ} (h : Ev main p s s' C)
    {r : Reg} (hr : r ∉ cmdTouchesR p) : s'.reg r = s.reg r := by
  obtain ⟨n, he, _⟩ := h
  exact Eval.reg_frame he hr

/-! ## Unfolding `sqrtStep` -/

theorem sqrtStep_snd (S r rem : ℕ) (x y : Bool) :
    (SG.sqrtStep S r rem x y).2.1
      = 2 * r + (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 1 else 0) := by
  unfold SG.sqrtStep
  by_cases h : 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) <;> simp [h]

theorem sqrtStep_trd (S r rem : ℕ) (x y : Bool) :
    (SG.sqrtStep S r rem x y).2.2
      = 4 * rem + (2 * x.toNat + y.toNat)
        - (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 4 * r + 1 else 0) := by
  unfold SG.sqrtStep
  by_cases h : 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) <;> simp [h]

/-- An even, nonempty list is a pair followed by a list. -/
theorem even_ne_nil {rest : List Bool} (h : rest.length % 2 = 0) (hne : rest ≠ []) :
    ∃ x y rest', rest = x :: y :: rest' := by
  rcases rest with _ | ⟨x, rest⟩
  · exact absurd rfl hne
  rcases rest with _ | ⟨y, rest'⟩
  · simp at h
  · exact ⟨x, y, rest', rfl⟩

/-- The value of a least-significant-first pair-then-list. -/
theorem ofBits_pair_append (x y : Bool) (l : List Bool) :
    ofBits (y :: x :: l) = 4 * ofBits l + (2 * x.toNat + y.toNat) := by
  rw [ofBits_cons, ofBits_cons]; ring

/-! ## The loop invariant -/

/-- Invariant of the square-root loop.

* `rest` — the radicand bits not yet read, most significant first (on `sA`, above its marker);
* `rb` — the current remainder `rem = S - r ^ 2`, least significant first (on `sB`);
* `rc` — the current root `r`, least significant first (on `sC`);
* `S` — the value of the part of the radicand already read;
* `bval bs = bval rest + 2 ^ rest.length * S` — `S` really is that prefix's value, the whole
  radicand being `bs` (`bs` is most significant first, so `bval` is its value).

The two length fields are for the cost bound only: the data regions never grow beyond the total. -/
structure Inv (bs : List Bool) (bA bB bC bP bQ bR bS : List Glyph) (s₀ s : State)
    (rest rb rc : List Bool) (S rem r : ℕ) : Prop where
  hA : s.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA
  hB : s.stk sB = rb.map Glyph.bit ++ Glyph.mk sB :: bB
  hC : s.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC
  hP : s.stk sP = Glyph.mk sP :: bP
  hQ : s.stk sQ = Glyph.mk sQ :: bQ
  hR : s.stk sR = Glyph.mk sR :: bR
  hS : s.stk sS = Glyph.mk sS :: bS
  hfr : Frame7 s₀ s
  hBv : ofBits rb = rem
  hCv : ofBits rc = r
  hrel : SG.bval bs = SG.bval rest + 2 ^ rest.length * S
  hlo : r ^ 2 ≤ S
  hhi : S < (r + 1) ^ 2
  hrem : rem = S - r ^ 2
  hbl : rb.length + rest.length ≤ bs.length
  hcl : rc.length + rest.length ≤ bs.length
  hpar : rest.length % 2 = 0

/-! ## More small helpers -/

/-- `ofBits` of `true :: rc` in terms of the value of `rc`. -/
theorem ofBits_true_cons (rc : List Bool) (r : ℕ) (h : ofBits rc = r) :
    ofBits (true :: rc) = 2 * r + 1 := by
  have ht : (true : Bool).toNat = 1 := rfl
  rw [ofBits_cons, h, ht]; ring

/-- `ofBits` of `false :: rc` in terms of the value of `rc`. -/
theorem ofBits_false_cons (rc : List Bool) (r : ℕ) (h : ofBits rc = r) :
    ofBits (false :: rc) = 2 * r := by
  have hf : (false : Bool).toNat = 0 := rfl
  rw [ofBits_cons, h, hf]; ring

/-- `ofBits` of `true :: false :: rc` in terms of the value of `rc`. -/
theorem ofBits_true_false_cons (rc : List Bool) (r : ℕ) (h : ofBits rc = r) :
    ofBits (true :: false :: rc) = 4 * r + 1 := by
  have ht : (true : Bool).toNat = 1 := rfl
  have hf : (false : Bool).toNat = 0 := rfl
  rw [ofBits_cons, ofBits_cons, h, ht, hf]; ring

theorem sqrtStep_fst (S r rem : ℕ) (x y : Bool) :
    (SG.sqrtStep S r rem x y).1 = 4 * S + (2 * x.toNat + y.toNat) := by
  unfold SG.sqrtStep
  by_cases h : 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) <;> simp [h]

theorem max_add_two (a b : ℕ) : max (a + 2) (b + 2) = max a b + 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by omega)]
  · rw [max_eq_left h, max_eq_left (by omega)]

/-- A marker of `Glyph` is never `eos`. -/
theorem mkNeEos (k : Stk) : Glyph.mk k ≠ Glyph.eos := fun h => by cases h

/-- Every glyph of `l.map Glyph.bit` differs from every marker. -/
theorem memMapBitNeMk (l : List Bool) (k : Stk) :
    ∀ g ∈ l.map Glyph.bit, g ≠ Glyph.mk k := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
  intro h
  cases h

/-- Every glyph of the *reversal* of `l.map Glyph.bit` differs from every marker. -/
theorem memMapBitNeMk_rev (l : List Bool) (k : Stk) :
    ∀ g ∈ (l.map Glyph.bit).reverse, g ≠ Glyph.mk k := by
  intro g hg
  rw [List.mem_reverse] at hg
  exact memMapBitNeMk l k g hg

/-- Any of `sA … sS` is one of `sA … sS`. -/
theorem seven_mem {a : Stk} (ha : a = sA ∨ a = sB ∨ a = sC ∨ a = sP ∨ a = sQ ∨ a = sR ∨ a = sS)
    {j : Stk} (hj : j = a) : j = sA ∨ j = sB ∨ j = sC ∨ j = sP ∨ j = sQ ∨ j = sR ∨ j = sS := by
  subst hj; exact ha

/-- `Frame7` from a program that only keeps the stacks of an explicit set. -/
theorem frame7_of_keeps1 {s t : State} {a : Stk}
    (ha : a = sA ∨ a = sB ∨ a = sC ∨ a = sP ∨ a = sQ ∨ a = sR ∨ a = sS)
    (h : ∀ j : Stk, j ≠ a → t.stk j = s.stk j) : Frame7 s t := by
  intro j hjA hjB hjC hjP hjQ hjR hjS
  refine h j ?_
  rcases ha with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption

theorem frame7_of_keeps3CL {s t : State} {a b c : Stk}
    (ha : a = sA ∨ a = sB ∨ a = sC ∨ a = sP ∨ a = sQ ∨ a = sR ∨ a = sS)
    (hb : b = sA ∨ b = sB ∨ b = sC ∨ b = sP ∨ b = sQ ∨ b = sR ∨ b = sS)
    (hc : c = sA ∨ c = sB ∨ c = sC ∨ c = sP ∨ c = sQ ∨ c = sR ∨ c = sS)
    (h : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ c → t.stk j = s.stk j) : Frame7 s t := by
  intro j hjA hjB hjC hjP hjQ hjR hjS
  refine h j ?_ ?_ ?_
  · rcases ha with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hb with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hc with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption

/-- `Frame7` from a program that only keeps the stacks of an explicit 4-element set. -/
theorem frame7_of_keeps4CL {s t : State} {a b c d : Stk}
    (ha : a = sA ∨ a = sB ∨ a = sC ∨ a = sP ∨ a = sQ ∨ a = sR ∨ a = sS)
    (hb : b = sA ∨ b = sB ∨ b = sC ∨ b = sP ∨ b = sQ ∨ b = sR ∨ b = sS)
    (hc : c = sA ∨ c = sB ∨ c = sC ∨ c = sP ∨ c = sQ ∨ c = sR ∨ c = sS)
    (hd : d = sA ∨ d = sB ∨ d = sC ∨ d = sP ∨ d = sQ ∨ d = sR ∨ d = sS)
    (h : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ c → j ≠ d → t.stk j = s.stk j) : Frame7 s t := by
  intro j hjA hjB hjC hjP hjQ hjR hjS
  refine h j ?_ ?_ ?_ ?_
  · rcases ha with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hb with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hc with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
  · rcases hd with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> assumption

/-! ## Small `Ev` blocks -/

/-- `set r g; push k r` pushes the glyph `g` on `k`. -/
theorem evSetPush (main : Cmd) (k : Stk) (r : Reg) (g : Glyph) (s : State) :
    ∃ s', Ev main (.seq (.set r g) (.push k r)) s s' 2 ∧
      s'.stk k = g :: s.stk k ∧ (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  let u1 : State := ⟨Function.update s.reg r g, s.stk⟩
  let u2 : State := ⟨u1.reg, Function.update u1.stk k (u1.reg r :: u1.stk k)⟩
  have e1 : Ev main (.set r g) s u1 1 := ev_set main r g s
  have e2 : Ev main (.push k r) u1 u2 1 := ev_push main k r u1
  refine ⟨u2, Ev.seq e1 e2, ?_, ?_⟩
  · simp only [u2, u1, Function.update_self]
  · intro j hj
    simp only [u2, u1, Function.update_apply]
    simp [hj]

/-- Two pops off one stack. -/
theorem evPop2 (main : Cmd) (k : Stk) (r1 r2 : Reg) (h12 : r1 ≠ r2) (s : State) :
    ∃ s', Ev main (.seq (.pop k r1) (.pop k r2)) s s' 2 ∧
      s'.stk k = (s.stk k).tail.tail ∧
      s'.reg r1 = (s.stk k).headD Glyph.eos ∧
      s'.reg r2 = (s.stk k).tail.headD Glyph.eos ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  let u1 : State := ⟨Function.update s.reg r1 ((s.stk k).headD .eos),
      Function.update s.stk k (s.stk k).tail⟩
  let u2 : State := ⟨Function.update u1.reg r2 ((u1.stk k).headD .eos),
      Function.update u1.stk k (u1.stk k).tail⟩
  have e1 : Ev main (.pop k r1) s u1 1 := ev_pop main k r1 s
  have e2 : Ev main (.pop k r2) u1 u2 1 := ev_pop main k r2 u1
  refine ⟨u2, Ev.seq e1 e2, ?_, ?_, ?_, ?_⟩
  · simp only [u2, u1, Function.update_self]
  · simp only [u2, u1, Function.update_apply]
    simp [h12]
  · simp only [u2, u1, Function.update_self]
  · intro j hj
    simp only [u2, u1, Function.update_apply]
    simp [hj]

/-- Two pushes onto one stack. -/
theorem evPush2 (main : Cmd) (k : Stk) (r1 r2 : Reg) (s : State) :
    ∃ s', Ev main (.seq (.push k r1) (.push k r2)) s s' 2 ∧
      s'.stk k = s.reg r2 :: s.reg r1 :: s.stk k ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  let u1 : State := ⟨s.reg, Function.update s.stk k (s.reg r1 :: s.stk k)⟩
  let u2 : State := ⟨u1.reg, Function.update u1.stk k (u1.reg r2 :: u1.stk k)⟩
  have e1 : Ev main (.push k r1) s u1 1 := ev_push main k r1 s
  have e2 : Ev main (.push k r2) u1 u2 1 := ev_push main k r2 u1
  refine ⟨u2, Ev.seq e1 e2, ?_, ?_⟩
  · simp only [u2, u1, Function.update_self]
  · intro j hj
    simp only [u2, u1, Function.update_apply]
    simp [hj]

/-- `rLoop k T none r` drops the region of `k` above the marker `T`. -/
theorem rLoopDrop (main : Cmd) (k : Stk) (T : Glyph) (r : Reg)
    (gs below : List Glyph) (s : State) (hT : T ≠ Glyph.eos) (hgs : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ s', Ev main (SG.rLoop k T none r) s s' (7 + gs.length * 5) ∧
      s'.stk k = T :: below ∧ s'.reg r = T ∧
      (∀ r' : Reg, r' ≠ r → s'.reg r' = s.reg r') ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨_, ⟨_, SG.dLoop_eval main k T r hT gs below s hstk hgs, le_rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [SG.dSt]
  · simp [SG.dSt]
  · intro r' hr'
    simp only [SG.dSt, Function.update_apply]
    simp [hr']
  · intro j hj
    simp only [SG.dSt, Function.update_apply]
    simp [hj]

/-- `rLoop k T (some d) r` moves (reversing) the region of `k` above `T` onto `d`. -/
theorem rLoopMove (main : Cmd) (k d : Stk) (T : Glyph) (r : Reg)
    (gs below : List Glyph) (s : State) (hT : T ≠ Glyph.eos) (hdk : d ≠ k)
    (hgs : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ s', Ev main (SG.rLoop k T (some d) r) s s' (7 + gs.length * 5) ∧
      s'.stk d = gs.reverse ++ s.stk d ∧ s'.stk k = T :: below ∧ s'.reg r = T ∧
      (∀ r' : Reg, r' ≠ r → s'.reg r' = s.reg r') ∧
      (∀ j : Stk, j ≠ k → j ≠ d → s'.stk j = s.stk j) := by
  refine ⟨_, ⟨_, SG.mLoop_eval main k T d r hT hdk gs below s hstk hgs, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SG.mSt]
  · simp [SG.mSt, Ne.symm hdk]
  · simp [SG.mSt]
  · intro r' hr'
    simp only [SG.mSt, Function.update_apply]
    simp [hr']
  · intro j hj1 hj2
    simp only [SG.mSt, Function.update_apply]
    simp [hj1, hj2]

end Work.IntLib.SqrtGcd
