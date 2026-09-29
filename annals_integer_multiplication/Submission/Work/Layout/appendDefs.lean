import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

/-!
# Layout area: definitions and helpers for the `appendWord` list word

`appendWord` is the `LayoutLib` list word that appends two lists of values on stack 0:
`ofList xs :: ofList ys :: rest ↦ ofList (xs ++ ys) :: rest`, touching only the encoding of `xs`.

The word (`Work.Layout.appendP`) is built from `Work.Layout.mvVal` (which moves one self-delimiting
value between two stacks) and works in three phases, using stacks 1 (`elems`), 2 (`xs` list) and
3, 4 (`mvVal` scratches):

* **phase 0**: `mvVal 0 2 3 4` moves `ofList xs` aside to stack 2, leaving stack 0 = `ofList ys :: rest`;
  on stack 1 (which receives the elements) a sentinel `gSent` is pushed first;
* **phase 1** (`p1`): walk `ofList xs` on stack 2 — while its top glyph is `Glyph.cons`, pop it and
  move the element (with `mvVal 2 1 3 4`) to stack 1, preceded by a marker `gMark`; at the terminator
  `Glyph.nil` pop it and stop.  Invariant: stack 1 = `elsEnc mzs (gSent :: C1)`.
* **phase 2** (`p2`): while the top glyph of stack 1 is `gMark`, pop the marker, move the element to
  stack 0 (`mvVal 1 0 3 4`) and prepend a `cons` glyph (`pushG 0 Glyph.cons`), consing it onto the
  current top value of stack 0.  Invariant: stack 0 = `lstEnc (p ++ ys) ++ C0`.
* **final**: pop the sentinel from stack 1.

Both loops are guarded by the flag register `rFl = 5`, which no other word of the library writes.

This file is pure definitions and elementary lemmas (`sorry`-free); the two loop lemmas are
`Work.Layout.appendPhase1`, `Work.Layout.appendPhase2`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Glyph-level encodings -/

/-- Flag register of the append word.  Distinct from every register written by `mvVal`/`mvA`/`mvB`
(`rLoopG = 0`, `rA = 1`, `rB = 2`, `rC = 3`, `rD = 4`). -/
def rFl : Reg := 5

/-- Glyph encoding of a list of values: `cons`, `v.enc` for each `v`, then the terminator `nil`.
`lstEnc zs = (ofList zs).enc`. -/
def lstEnc : List Val → List Glyph
  | [] => [Glyph.nil]
  | v :: zs => (Glyph.cons :: v.enc) ++ lstEnc zs

/-- Glyph content of the element stack: for each element (top first) its marker `gMark` and its
encoding, followed by the rest `C`. -/
def elsEnc : List Val → List Glyph → List Glyph
  | [], C => C
  | v :: zs, C => (gMark :: v.enc) ++ elsEnc zs C

@[simp] theorem lstEnc_nil : lstEnc ([] : List Val) = [Glyph.nil] := rfl
@[simp] theorem lstEnc_cons (v : Val) (zs : List Val) :
    lstEnc (v :: zs) = (Glyph.cons :: v.enc) ++ lstEnc zs := rfl
@[simp] theorem elsEnc_nil (C : List Glyph) : elsEnc ([] : List Val) C = C := rfl
@[simp] theorem elsEnc_cons (v : Val) (zs : List Val) (C : List Glyph) :
    elsEnc (v :: zs) C = (gMark :: v.enc) ++ elsEnc zs C := rfl

/-- `(ofList zs).enc = lstEnc zs`. -/
theorem ofList_enc (zs : List Val) : (ofList zs).enc = lstEnc zs := by
  induction zs with
  | nil => rfl
  | cons v zs ih =>
    rw [show ofList (v :: zs) = Val.cons v (ofList zs) from rfl]
    simp [Val.enc, lstEnc, ih]

/-- A value stack whose head is `ofList zs`. -/
theorem encs_ofList (zs : List Val) (rest : List Val) :
    encs (ofList zs :: rest) = lstEnc zs ++ encs rest := by
  simp [encs, ofList_enc]

/-- `lstEnc` for a cons, with a tail glyph list (associativity-friendly form). -/
theorem lstEnc_cons_append (v : Val) (zs : List Val) (C : List Glyph) :
    lstEnc (v :: zs) ++ C = Glyph.cons :: (v.enc ++ (lstEnc zs ++ C)) := by
  simp [lstEnc_cons, List.append_assoc]

/-- `elsEnc` for a cons, with a tail glyph list (associativity-friendly form). -/
theorem elsEnc_cons_append (v : Val) (zs : List Val) (C : List Glyph) :
    elsEnc (v :: zs) C = gMark :: (v.enc ++ elsEnc zs C) := by
  simp [elsEnc_cons]

/-- `elsEnc` is a fold: concatenation of the value list. -/
theorem elsEnc_append (l₁ l₂ : List Val) (C : List Glyph) :
    elsEnc (l₁ ++ l₂) C = elsEnc l₁ (elsEnc l₂ C) := by
  induction l₁ with
  | nil => simp
  | cons v l₁ ih => simp [ih]

/-- Size of a list of values as encoded by `lstEnc`. -/
theorem vsz_ofList (zs : List Val) : vsz (ofList zs) = (zs.map vsz).sum + zs.length + 1 := by
  induction zs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v zs ih =>
    have h1 : vsz (ofList (v :: zs)) = vsz v + vsz (ofList zs) + 1 := by
      show (Val.enc (ofList (v :: zs))).length = _
      rw [show ofList (v :: zs) = Val.cons v (ofList zs) from rfl]
      show ((Val.cons v (ofList zs)).enc).length = _
      simp [vsz, Val.enc, List.length_append]
    rw [h1, ih]
    simp [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- One `cons` layer. -/
theorem vsz_ofList_cons_ap (v : Val) (zs : List Val) :
    vsz (ofList (v :: zs)) = vsz v + vsz (ofList zs) + 1 := by
  rw [vsz_ofList, vsz_ofList]
  simp [List.map_cons, List.sum_cons, List.length_cons]
  omega

/-- Reversing a list does not change the size of its `ofList`. -/
theorem vsz_ofList_reverse_ap (zs : List Val) : vsz (ofList zs.reverse) = vsz (ofList zs) := by
  rw [vsz_ofList, vsz_ofList]
  simp [List.map_reverse, List.sum_reverse]

/-! ## The programs -/

/-- Push the constant glyph `c` on stack `k` (through register `rB`). -/
def pushG (k : Stk) (c : Glyph) : Cmd := seqs [.set rB c, .push k rB]

/-- Phase 1 body, `Glyph.cons` case: consume the `cons` glyph, move the element to stack 1 behind a
marker, and continue. -/
def p1Cons : Cmd := seqs [.pop 2 rA, mvVal 2 1 3 4, pushG 1 gMark, .set rFl Glyph.cons]

/-- Phase 1 body, terminator case: consume the `nil` glyph and stop. -/
def p1Nil : Cmd := seqs [.pop 2 rA, .set rFl Glyph.eos]

/-- Phase 1 loop body: look at the top glyph of stack 2. -/
def p1Body : Cmd := seqs [.peek 2 rA, .ite rA Glyph.cons p1Cons p1Nil]

/-- Phase 1 loop: unpack `ofList xs` from stack 2 onto the element stack 1. -/
def p1Loop : Cmd := .loop rFl Glyph.cons p1Body

/-- Phase 1: enter the loop. -/
def p1 : Cmd := .seq (.set rFl Glyph.cons) p1Loop

/-- Phase 2 body. -/
def p2Body : Cmd := seqs [.peek 1 rA, .ite rA gMark
  (seqs [.pop 1 rA, mvVal 1 0 3 4, pushG 0 Glyph.cons, .set rFl gMark]) (.set rFl Glyph.eos)]

/-- Phase 2 loop: cons the elements of stack 1 onto the top value of stack 0. -/
def p2Loop : Cmd := .loop rFl gMark p2Body

/-- Phase 2: enter the loop. -/
def p2 : Cmd := .seq (.set rFl gMark) p2Loop

/-- **The append word**: stack 0 = `ofList xs :: ofList ys :: rest ↦ ofList (xs ++ ys) :: rest`. -/
def appendP : Cmd := seqs [mvVal 0 2 3 4, pushG 1 gSent, p1, p2, .pop 1 rA]

/-! ## Frames -/

theorem cmdTouches_p1Loop : cmdTouches p1Loop ⊆ ({1, 2, 3, 4} : Finset Stk) := by decide

theorem cmdTouches_p2Loop : cmdTouches p2Loop ⊆ ({0, 1, 3, 4} : Finset Stk) := by decide

theorem cmdTouches_p1 : cmdTouches p1 ⊆ ({1, 2, 3, 4} : Finset Stk) := by decide

theorem cmdTouches_p2 : cmdTouches p2 ⊆ ({0, 1, 3, 4} : Finset Stk) := by decide

theorem cmdTouches_appendP : cmdTouches appendP ⊆ ({0, 1, 2, 3, 4} : Finset Stk) := by decide

/-- `k ∉ {1,2,3,4}` from the four inequalities. -/
theorem notMem_1234 {k : Stk} (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) :
    k ∉ ({1, 2, 3, 4} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- `k ∉ {0,1,3,4}` from the four inequalities. -/
theorem notMem_0134 {k : Stk} (h0 : k ≠ 0) (h1 : k ≠ 1) (h3 : k ≠ 3) (h4 : k ≠ 4) :
    k ∉ ({0, 1, 3, 4} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- `k ∉ {0,1,2,3,4}` from the five inequalities. -/
theorem notMem_01234_ap {k : Stk} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3)
    (h4 : k ≠ 4) : k ∉ ({0, 1, 2, 3, 4} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ## Strengthened `mvVal` (all five stacks pinned) -/

/-- `mvVal` moves one value from stack `a` to stack `b` (normal order); both scratch stacks `c`, `d`
are *restored*, and so is every other stack. -/
theorem mvVal_ev_all {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Ev main (mvVal a b c d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    mvB_ev (main := main) hbc (G := v.enc.reverse) (C := X c) (B := B)
      (gMark_not_mem_enc_rev v) hc₁ hb₁
  have hmain : Ev main (mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold mvVal
    exact Ev.seq h1 h2
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hn₂' : n₂ ≤ 4 * (vsz v + 1) + 3 := by rw [← hlen]; exact hn₂
  have hcost : n₁ + n₂ ≤ 16 * (vsz v + 1) := by
    have h₁ : n₁ ≤ 10 * vsz v + 10 := hn₁
    have hv := one_le_vsz v
    omega
  refine ⟨s₂, _, hmain, hcost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ a hac hab, ha₁]
  · rw [hb₂, List.reverse_reverse]
  · rw [hc₂]
  · rw [hf₂ d hcd.symm hbd.symm, hd₁]
  · intro k hka hkb hkc hkd
    rw [hf₂ k hkc hkb, hf₁ k hka hkc hkd]

end Work.Layout
