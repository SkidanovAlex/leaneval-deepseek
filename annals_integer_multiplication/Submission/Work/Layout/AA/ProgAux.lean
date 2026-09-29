import Mathlib
import Submission.Work.Layout.AA.Comp
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.PureDefs
import Submission.Work.Layout.AA.clearTo_ev
import Submission.Work.Layout.AA.copyIntTo_ev
import Submission.Work.Layout.AA.halveInt_ev
import Submission.Work.Layout.AA.isOneInt_ev
import Submission.Work.Layout.AA.isZeroInt_ev
import Submission.Work.Layout.AA.moveTo_ev
import Submission.Work.Layout.AA.prependTo_ev
import Submission.Work.Layout.AA.unconsTo_ev
import Submission.Work.Layout.AA.copyIntB1_loop
import Submission.Work.Layout.AA.transposeC_eq
import Submission.Work.Layout.AA.slices_eq_blocks
import Submission.Work.Layout.AA.unslices_eq_blocks

/-!
# Common definitions and easy facts for the `prog_ev` development

This file collects the definitions (`jobVal`, `UC`, …) and easy lemmas (marker-freeness,
`push`/`pushNil`/`pushCons`, the strengthened `mvVal`, slicing facts) shared by the pieces of the
proof of `Work.Layout.AA.prog_ev`.

## State convention

Every working stack `k ≠ 0` of the program carries a boundary marker `gMark = Glyph.mk 7` pushed
once by the `prologue`; everything above the *first* marker found from the top is "data", everything
below is preserved forever (restored by the `epilogue`).  Data above a marker is built out of `Val`
encodings and `nil` glyphs (hence contains no marker; see `MFree`) and specs are stated as

  `X k = <prefix> ++ G k ++ gMark :: Z k`

where `<prefix>` is the data currently being manipulated, `G k` is "garbage" from earlier operations
(never read; must be marker-free when a clear routine scans down to the marker) and `Z k` is
everything below the marker.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH
open Work.Layout

/-! ## 1. Marker-freeness -/

/-- a list of glyphs contains no boundary marker -/
def MFree (l : List Glyph) : Prop := gMark ∉ l

theorem mfree_nil : MFree [] := by simp [MFree]

theorem MFree.append {l₁ l₂ : List Glyph} (h₁ : MFree l₁) (h₂ : MFree l₂) :
    MFree (l₁ ++ l₂) := fun hx => (List.mem_append.mp hx).elim h₁ h₂

theorem MFree.cons {g : Glyph} {l : List Glyph} (hg : g ≠ gMark) (h : MFree l) :
    MFree (g :: l) := by
  intro hx
  rcases List.mem_cons.mp hx with h1 | h1
  · exact hg h1.symm
  · exact h h1

theorem mfree_enc (v : Val) : MFree v.enc := gMark_not_mem_enc v

theorem mfree_encs (vs : List Val) : MFree (encs vs) := by
  induction vs with
  | nil => exact mfree_nil
  | cons v vs ih => exact MFree.append (mfree_enc v) ih

theorem mfree_ofList (L : List Val) : MFree (ofList L).enc := mfree_enc _

theorem mfree_append_ofList (L : List Val) (G : List Glyph) (h : MFree G) :
    MFree ((ofList L).enc ++ G) := MFree.append (mfree_ofList L) h

/-! ## 2. Job values and the DFS semantics -/

/-- a DFS job: `cons (int C) (ofList L)` -/
def jobVal (C : ℕ) (L : List Val) : Val := .cons (.int (C : ℤ)) (ofList L)

/-- the columns of the flat array `L` of shape `(L.length / C) × C`: the slices emitted by the DFS
for the job `(C, L)`, in `sSl` order (the first emitted slice is the head) -/
def jobCols (C : ℕ) (L : List Val) : List (List Val) := colsOf (L.length / C) C L

/-- the contribution of a list of pending jobs (top of the job stack first) to the content of `sSl` -/
def pend : List (ℕ × List Val) → List (List Val)
  | [] => []
  | (C, L) :: rest => (jobCols C L).reverse ++ pend rest

theorem pend_cons (C : ℕ) (L : List Val) (rest : List (ℕ × List Val)) :
    pend ((C, L) :: rest) = (jobCols C L).reverse ++ pend rest := rfl

/-- one DFS step: discard a `0`-counter job, emit a `1`-counter job, split a bigger one -/
def dfsStep (p : ℕ × List Val) (rest : List (ℕ × List Val)) : List (ℕ × List Val) :=
  if p.1 ≤ 1 then rest
  else
    ((p.1 / 2, ((rowsOf (p.2.length / p.1) p.1 p.2).map (fun r => r.take (p.1 / 2))).flatten) ::
      ((p.1 - p.1 / 2, ((rowsOf (p.2.length / p.1) p.1 p.2).map (fun r => r.drop (p.1 / 2))).flatten) :: rest))

/-- the flat array of `R` rows of length `C`, in row-major order, has `rowsOf R C` as rows -/
def Rows (R C : ℕ) : Prop := True

/-! ## 3. A uniform cost bound -/

/-- uniform cost bound: `V` = total size (`vsz (ofList data)`) of the data being moved, `R` = a
number of rows / outer iterations, `Ks` = a bound on `isz` of the counters involved. -/
def UC (V R Ks : ℕ) : ℕ := 1000 * (V + 1) * (Ks + 1) + 1000 * (R + 1) * (Ks + 1) + 100

/-! ## 4. easy `push` specifications -/

/-- `Work.Kernel.pushGlyphs l k r` pushes the glyphs of `l` (first element first, so the top of `k`
becomes `l.reverse`) -/
theorem pushGlyphs_ev (main : HvdH.Cmd) (l : List HvdH.Glyph) (k : HvdH.Stk) (r : HvdH.Reg)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) :
    ∃ s' n, Work.Layout.Ev main (Work.Kernel.pushGlyphs l k r) ⟨g, X⟩ s' n ∧
      n ≤ 2 * l.length + 1 ∧ s'.stk k = l.reverse ++ X k ∧
      (∀ j, j ≠ k → s'.stk j = X j) := by
  have h1 : Work.Layout.Ev main (Work.Kernel.pushGlyphs l k r) ⟨g, X⟩
      (Work.Kernel.pushGlyphsState l k r ⟨g, X⟩) (Work.Kernel.pushGlyphsCost l) :=
    ⟨_, Work.Kernel.eval_pushGlyphs main l k r ⟨g, X⟩, le_rfl⟩
  refine ⟨_, _, h1, ?_, ?_, ?_⟩
  · rw [Work.Kernel.pushGlyphsCost_eq]
  · rw [Work.Kernel.pushGlyphsState_stk]; simp
  · intro j hj
    rw [Work.Kernel.pushGlyphsState_stk, if_neg hj]

/-- `pushNil k r` pushes the empty list (`nil`) on stack `k` -/
theorem pushNil_ev (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) :
    ∃ s' n, Work.Layout.Ev main (pushNil k r) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk k = (ofList ([] : List Val)).enc ++ X k ∧
      (∀ j, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s', n, h1, h2, h3, h4⟩ := pushGlyphs_ev main [Glyph.nil] k r g X
  refine ⟨s', n, h1, ?_, ?_, h4⟩
  · simp only [List.length_singleton] at h2; omega
  · rw [h3]; rfl

/-- `pushCons k` pushes a `cons` glyph on stack `k` -/
theorem pushCons_ev (main : HvdH.Cmd) (k : HvdH.Stk)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) :
    ∃ s' n, Work.Layout.Ev main (pushCons k) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk k = Glyph.cons :: X k ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s', n, h1, h2, h3, h4⟩ := pushGlyphs_ev main [Glyph.cons] k rQ2 g X
  refine ⟨s', n, h1, ?_, ?_, h4⟩
  · simp only [List.length_singleton] at h2; omega
  · rw [h3]; rfl

/-- `pushCons` after a value has been prepended: it turns the top value `v` followed by the list
`ofList L` into the list `ofList (v :: L)` -/
theorem pushCons_val_ev (main : HvdH.Cmd) (k : HvdH.Stk) (v : Val) (L : List Val) (G : List Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (hX : X k = v.enc ++ (ofList L).enc ++ G) :
    ∃ s' n, Work.Layout.Ev main (pushCons k) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk k = (ofList (v :: L)).enc ++ G ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s', n, h1, h2, h3, h4⟩ := pushCons_ev main k g X
  refine ⟨s', n, h1, h2, ?_, h4⟩
  rw [h3, hX]
  rfl

/-! ## 5. strengthened `mvVal` (scratch stacks restored) -/

/-- `mvVal a b c d` moves one value from `a` to `b`, restoring the scratch stacks `c` and `d`
exactly. -/
theorem mvVal_ev' {main : HvdH.Cmd} {a b c d : HvdH.Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {v : HvdH.Val} {A B : List HvdH.Glyph}
    (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k, k ≠ a → k ≠ b → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    Work.Layout.mvB_ev (main := main) hbc (G := v.enc.reverse) (C := X c) (B := B)
      (Work.Layout.gMark_not_mem_enc_rev v) hc₁ hb₁
  have hlen : (v.enc.reverse).length = HvdH.vsz v := by simp [HvdH.vsz]
  have hn₂' : n₂ ≤ 4 * (HvdH.vsz v + 1) + 3 := by rw [← hlen]; exact hn₂
  have hmain : Work.Layout.Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold Work.Layout.mvVal
    exact Work.Layout.Ev.seq h1 h2
  have hcost : n₁ + n₂ ≤ 16 * (HvdH.vsz v + 1) := by
    have h₁ : n₁ ≤ 10 * HvdH.vsz v + 10 := hn₁
    have hv := Work.Layout.one_le_vsz v
    omega
  refine ⟨s₂, _, hmain, hcost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ a hac hab]; exact ha₁
  · rw [hb₂, List.reverse_reverse]
  · exact hc₂
  · rw [hf₂ d (Ne.symm hcd) (Ne.symm hbd), hd₁]
  · intro k hka hkb
    by_cases hkc : k = c
    · subst hkc; rw [hc₂]
    · by_cases hkd : k = d
      · subst hkd; rw [hf₂ k hkc hkb, hd₁]
      · rw [hf₂ k hkc hkb]
        exact hf₁ k hka hkc hkd


/-! ## 7. more pure definitions -/

/-- the flat layout of the outputs of one group: this is the piece of `unslices` belonging to group
`a` (`unslices A n B outs` is the concatenation of `oneSeg n B outs a` over `a < A`). -/
def oneSeg (n B : ℕ) (outs : List (List Val)) (a : ℕ) : List Val :=
  ((List.range n).map fun i =>
    ((List.range B).map fun j => (outs.getD (a * B + j) []).getD i default)).flatten

/-- `slices` has `A*B` entries -/
theorem slices_length' (A m B : ℕ) (es : List Val) : (HvdH.slices A m B es).length = A * B := by
  simp [HvdH.slices]

/-- every entry of `slices` has length `m` -/
theorem slices_getD_length (A m B : ℕ) (es : List Val) (s : ℕ) (hs : s < A * B) :
    ((HvdH.slices A m B es).getD s []).length = m := by
  unfold HvdH.slices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hs)]
  simp

end Work.Layout.AA
