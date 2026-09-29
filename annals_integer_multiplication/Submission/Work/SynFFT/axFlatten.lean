import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# A clash-free copy of the Layout area's `flatten` word

`Submission/Work/Layout/flattenWord.lean` provides the flatten word used by the transpose assembly,
but its (and `flattenDefs`', and `flattenInnerLoop`'s) declarations live in the namespace
`Work.Layout`, which now also contains a *duplicate* `cmdTouches_mvVal` (in
`Work.Layout/chunksProof.lean` and `Work.Resample.PBChunk/chunksProof.lean`), so that no single
Lean environment can contain both the flatten word and the chunk word.

This file is a verbatim copy of the three flatten modules, moved to the namespace
`Work.SynFFT.AxFlat` so that it can be imported together with a chunk word.  Everything is
`sorry`-free; do not read any mathematical content into the copy.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.SynFFT.AxFlat

open HvdH
open Work.Layout


/-!
# Layout area: definitions for the `flattenWord` list word

`flatten` takes a list of lists of values `ofList (xss.map ofList)` on stack 0 and returns the
concatenation `ofList xss.flatten`, touching each glyph of the input `O(1)` times.

The word `flattenProg` works in three phases, using stacks

* `0` : the input (outer list of lists) and, at the end, the output;
* `1` : the element stack, whose bottom carries the sentinel `gMark`;
* `2` : a scratch stack holding the current inner list (phase 1) resp. the result accumulator
  (phase 3);
* `3`, `4` : the scratch stacks of `Work.Layout.mvVal`.

* **phase 1** (`flatOuterBody` loop): while the top glyph of stack 0 is `Glyph.cons`, pop it and move
  the inner list value to stack 2 (`mvVal 0 2 3 4`), then run the inner loop `flatInnerBody`: while
  the top glyph of stack 2 is `Glyph.cons`, pop it and move the element to the top of stack 1
  (`mvVal 2 1 3 4`).  At the terminator `Glyph.nil` the inner loop stops and pops it.
  Invariant: stack 1 = `encs zs ++ gMark :: _` where `zs` is the reverse of the flattening of the
  lists processed so far.
* **phase 2**: drop the final `nil` of the outer list; push the accumulator `nil` on stack 2.
* **phase 3** (`flatFoldBody` loop): while the top glyph of stack 1 is not `gMark`, move the value on
  top of stack 1 onto stack 2 (`mvVal 1 2 3 4`) and push a `cons` glyph in front of it (so stack 2
  grows the value `ofList` of the elements read so far).  At the sentinel the loop stops and the
  sentinel is popped.
* **final**: move the accumulator from stack 2 to stack 0 (`mvVal 2 0 3 4`).

Since stack 1 receives the elements of the inner lists in reading order, its top value at the end is
the last element of `xss.flatten`; the fold loop then rebuilds `ofList xss.flatten` bottom-up.

This file is pure definitions and elementary lemmas (`sorry`-free).
-/

set_option autoImplicit false


open HvdH

/-! ## Registers and costs -/

/-- flag register of the outer (unpacking) loop; distinct from the registers `0`--`4` used by `mvVal` -/
def rFlatOut : Reg := 5
/-- flag register of the inner (per-list) loop -/
def rFlatIn : Reg := 6
/-- flag register of the final cons-folding loop -/
def rFlatFold : Reg := 7

/-- Cost bound for the inner loop: one `mvVal`-move per element of `l` plus a final test. -/
def scanCost (l : List Val) : ℕ := (l.map (fun y => 16 * (vsz y + 1) + 5)).sum + 4

/-- Cost bound for the fold loop: one `mvVal`-move and one glyph push per element plus a final test. -/
def foldCost (l : List Val) : ℕ := (l.map (fun y => 16 * (vsz y + 1) + 6)).sum + 4

/-- Cost of one outer-loop iteration that processes the inner list `l` (body only, final test not
included). -/
def outerIterCost (l : List Val) : ℕ := 16 * (vsz (ofList l) + 1) + scanCost l + 8

/-- Cost bound for the outer loop: one iteration per inner list plus a final test. -/
def outerCost (xss : List (List Val)) : ℕ := (xss.map (fun l => outerIterCost l + 1)).sum + 4

/-! ## The program -/

/-- Inner loop body: if the top glyph of stack 2 is `cons`, pop it and move the element to stack 1;
at `nil` stop. -/
def flatInnerBody : Cmd :=
  .seq (.peek 2 rA)
    (.ite rA Glyph.nil
      (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB)
        (.seq (mvVal 2 1 3 4)
          (.set rFlatIn Glyph.cons))))

/-- Outer loop body: if the top glyph of stack 0 is `cons`, pop it, move the inner list value to
stack 2, run the inner loop, pop its terminator and continue; at `nil` stop. -/
def flatOuterBody : Cmd :=
  .seq (.peek 0 rA)
    (.ite rA Glyph.nil
      (.set rFlatOut Glyph.eos)
      (.seq (.pop 0 rB)
        (.seq (mvVal 0 2 3 4)
          (.seq (.set rFlatIn Glyph.cons)
            (.seq (.loop rFlatIn Glyph.cons flatInnerBody)
              (.seq (.pop 2 rA)
                (.set rFlatOut Glyph.cons)))))))

/-- Fold loop body: if the top glyph of stack 1 is the sentinel `gMark`, stop; otherwise move the top
value of stack 1 onto stack 2 and push a `cons` glyph in front of it. -/
def flatFoldBody : Cmd :=
  .seq (.peek 1 rA)
    (.ite rA gMark
      (.set rFlatFold Glyph.eos)
      (.seq (mvVal 1 2 3 4)
        (.seq (pushConst 2 Glyph.cons)
          (.set rFlatFold gMark))))

/-- **The flatten word.** -/
def flattenProg : Cmd :=
  .seq (pushConst 1 gMark)
    (.seq (.set rFlatOut Glyph.cons)
      (.seq (.loop rFlatOut Glyph.cons flatOuterBody)
        (.seq (.pop 0 rA)
          (.seq (pushConst 2 Glyph.nil)
            (.seq (.set rFlatFold gMark)
              (.seq (.loop rFlatFold gMark flatFoldBody)
                (.seq (.pop 1 rA)
                  (mvVal 2 0 3 4))))))))

/-! ## Elementaries about the encodings -/

theorem encs_cons' (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

theorem encs_append (l₁ l₂ : List Val) : encs (l₁ ++ l₂) = encs l₁ ++ encs l₂ := by
  simp [encs]

theorem ofList_nil' : ofList ([] : List Val) = .nil := rfl

theorem ofList_cons' (y : Val) (ys : List Val) : ofList (y :: ys) = .cons y (ofList ys) := rfl

theorem ofList_enc_nil : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

theorem ofList_enc_cons (y : Val) (ys : List Val) :
    (ofList (y :: ys)).enc = Glyph.cons :: (y.enc ++ (ofList ys).enc) := rfl

theorem ofList_enc_ne_nil (ys : List Val) : (ofList ys).enc ≠ [] := by
  cases ys with
  | nil => simp [ofList, Val.enc]
  | cons y ys => simp [ofList, Val.enc]

theorem headD_ofList_cons (y : Val) (ys : List Val) (A : List Glyph) :
    ((ofList (y :: ys)).enc ++ A).headD Glyph.eos = Glyph.cons := by
  rw [ofList_enc_cons]; rfl

theorem headD_ofList_nil (A : List Glyph) :
    ((ofList ([] : List Val)).enc ++ A).headD Glyph.eos = Glyph.nil := by
  rw [ofList_enc_nil]; rfl

theorem eq_nil_of_enc_cons_eq_nil {y : Val} {ys : List Val} {A : List Glyph}
    (h : (ofList (y :: ys)).enc ++ A = (ofList ([] : List Val)).enc ++ A) : False := by
  have h2 : Glyph.cons = Glyph.nil := by
    have := congrArg (fun l : List Glyph => l.headD Glyph.eos) h
    rwa [headD_ofList_cons, headD_ofList_nil] at this
  exact gcons_ne_nil h2

/-- The sentinel `gMark` does not occur in the encoding of a list of values. -/
theorem gMark_not_mem_encs (ys : List Val) : gMark ∉ encs ys := by
  intro h
  obtain ⟨l', hl'mem, hl'⟩ := List.mem_flatten.mp h
  obtain ⟨v, -, hv⟩ := List.mem_map.mp hl'mem
  exact gMark_not_mem_enc v (hv ▸ hl')

/-- The head of `v.enc ++ L` (any tail) is never the sentinel `gMark`. -/
theorem headD_enc_append_ne_gMark (v : Val) (L : List Glyph) :
    (v.enc ++ L).headD Glyph.eos ≠ gMark := by
  cases v with
  | int z =>
      by_cases hz : z < 0
      · rw [Val.enc, if_pos hz]
        exact fun h => gMark_ne_neg h.symm
      · rw [Val.enc, if_neg hz]
        exact fun h => gMark_ne_pos h.symm
  | nil => rw [Val.enc]; exact fun h => gMark_ne_nil h.symm
  | cons a b => rw [Val.enc]; exact fun h => gMark_ne_cons h.symm

/-- `encs (v :: vs) ++ L` starts with the encoding of `v`. -/
theorem headD_encs_cons_ne_gMark (v : Val) (vs : List Val) (L : List Glyph) :
    (encs (v :: vs) ++ L).headD Glyph.eos ≠ gMark := by
  rw [encs_cons', List.append_assoc]
  exact headD_enc_append_ne_gMark v _

/-- Splitting off the leading `cons` of a nonempty `ofList`. -/
theorem ofList_enc_cons_append (y : Val) (ys : List Val) (A : List Glyph) :
    (ofList (y :: ys)).enc ++ A = Glyph.cons :: (y.enc ++ ((ofList ys).enc ++ A)) := by
  rw [ofList_enc_cons, List.cons_append, List.append_assoc]

/-! ## The stacks the program touches -/

theorem cmdTouches_mvVal (a b c d : Stk) : cmdTouches (mvVal a b c d) = {a, b, c, d} := by
  rw [mvVal, cmdTouches, cmdTouches_mvA, cmdTouches_mvB]
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

theorem cmdTouches_flattenProg : cmdTouches flattenProg = {0, 1, 2, 3, 4} := by
  simp only [flattenProg, flatOuterBody, flatInnerBody, flatFoldBody, pushConst, seqs,
    cmdTouches, cmdTouches_mvVal]
  decide

/-- Membership test for the set of stacks the flatten word touches. -/
theorem notMem_01234 {k : Stk} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3)
    (h4 : k ≠ 4) : k ∉ ({0, 1, 2, 3, 4} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto



/-!
# `Layout.flattenInnerLoop`: the inner (per-inner-list) loop of `flattenProg`

`flatInnerBody` is the body of the loop that consumes one inner list: while the top
glyph of stack 2 is `Glyph.cons`, pop it and move the element (a whole `Val`) to stack 1; at
`Glyph.nil` stop (set the loop flag to `eos`).

This file proves that starting from
`X 2 = (ofList ys).enc ++ A`, `X 1 = encs arr ++ gMark :: B`
the loop runs `ys.length + 1` times at cost `scanCost ys`, ending with
`s'.stk 2 = (ofList []).enc ++ A`, `s'.stk 1 = encs (ys.reverse ++ arr) ++ gMark :: B`,
the scratch stacks 3, 4 restored, and the flag `rFlatIn` equal to `eos`.
-/

set_option autoImplicit false


open HvdH

/-! ## The two one-step lemmas for the inner-loop body -/

/-- the current inner list is exhausted (its encoding starts with `nil`): the body sets the flag to
`eos` and changes nothing else. -/
theorem flattenInnerLoop_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {A : List Glyph} (h2 : X 2 = (ofList ([] : List Val)).enc ++ A) :
    ∃ s' n, Ev main flatInnerBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 2 = X 2 ∧ s'.stk 1 = X 1 ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFlatIn = Glyph.eos := by
  have hhead : (X 2).headD Glyph.eos = Glyph.nil := by rw [h2]; rfl
  have h1 := ev_peek' (main := main) 2 rA g X
  rw [hhead] at h1
  have h2ev : Ev main (.ite rA Glyph.nil (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons))))
      ⟨Function.update g rA Glyph.nil, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rFlatIn Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp) (ev_set' (main := main) rFlatIn Glyph.eos _ X)
  have h3 : Ev main flatInnerBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rFlatIn Glyph.eos, X⟩ 3 := by
    unfold flatInnerBody
    exact Ev.seq h1 h2ev
  exact ⟨_, _, h3, by omega, rfl, rfl, rfl, rfl, by simp⟩

/-- there is still an element in the current inner list: pop the leading `cons` glyph of stack 2,
move the element onto the top of stack 1, and set the flag to `cons`. -/
theorem flattenInnerLoop_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {y : Val} {ys arr : List Val} {A B : List Glyph}
    (h2 : X 2 = (ofList (y :: ys)).enc ++ A) (h1 : X 1 = encs arr ++ gMark :: B) :
    ∃ s' n, Ev main flatInnerBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz y + 1) + 4 ∧
      s'.stk 2 = (ofList ys).enc ++ A ∧ s'.stk 1 = encs (y :: arr) ++ gMark :: B ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFlatIn = Glyph.cons := by
  have hhead : (X 2).headD Glyph.eos = Glyph.cons := by rw [h2]; rfl
  have htail : (X 2).tail = y.enc ++ ((ofList ys).enc ++ A) := by
    rw [h2, ofList_enc_cons, List.cons_append, List.tail_cons, List.append_assoc]
  have hpeek := ev_peek' (main := main) 2 rA g X
  rw [hhead] at hpeek
  have hpop : Ev main (.pop 2 rB) ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update g rA Glyph.cons) rB Glyph.cons,
        Function.update X 2 (X 2).tail⟩ 1 := by
    have h := ev_pop' (main := main) 2 rB (Function.update g rA Glyph.cons) X
    rw [hhead] at h
    exact h
  obtain ⟨s₃, n₃, hmv, hn₃, h3a, h3b, h3c, h3d, -⟩ :=
    mvVal_ev_full (main := main) (a := 2) (b := 1) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update (Function.update g rA Glyph.cons) rB Glyph.cons)
      (X := Function.update X 2 (X 2).tail) (v := y)
      (A := (ofList ys).enc ++ A) (B := encs arr ++ gMark :: B)
      (by simp only [stkFn_same, htail])
      (by simp only [stkFn_ne X (by decide : (1 : Stk) ≠ 2), h1])
  have hset : Ev main (.set rFlatIn Glyph.cons) s₃
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' (main := main) rFlatIn Glyph.cons s₃.reg s₃.stk
  have hbranch : Ev main (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons)))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      (1 + (n₃ + 1)) :=
    Ev.seq hpop (Ev.seq hmv hset)
  have hite : Ev main (.ite rA Glyph.nil (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons))))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      ((1 + (n₃ + 1)) + 1) :=
    Ev.iteF (by simp) hbranch
  have hbody : Ev main flatInnerBody ⟨g, X⟩
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      (1 + ((1 + (n₃ + 1)) + 1)) := by
    unfold flatInnerBody
    exact Ev.seq hpeek hite
  have hle : 1 + ((1 + (n₃ + 1)) + 1) ≤ 16 * (vsz y + 1) + 4 := by omega
  obtain ⟨n, hev, hle'⟩ := hbody.mono hle
  refine ⟨_, n, ⟨n, hev, le_rfl⟩, hle', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3a]
  · rw [h3b]
    simp only [encs_cons', List.append_assoc]
  · rw [h3c]
    exact Function.update_of_ne (by decide : (3 : Stk) ≠ 2) (X 2).tail X
  · rw [h3d]
    exact Function.update_of_ne (by decide : (4 : Stk) ≠ 2) (X 2).tail X
  · simp

/-! ## The loop -/

theorem flattenInnerLoop {main : HvdH.Cmd} :
    ∀ (ys : List HvdH.Val) (arr : List HvdH.Val) (A B : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      g rFlatIn = HvdH.Glyph.cons →
      X 2 = (HvdH.ofList ys).enc ++ A →
      X 1 = HvdH.encs arr ++ Work.Layout.gMark :: B →
      ∃ s', Work.Layout.loopRuns main rFlatIn HvdH.Glyph.cons
          flatInnerBody (ys.length + 1) ⟨g, X⟩ s' (scanCost ys) ∧
        s'.stk 2 = (HvdH.ofList ([] : List HvdH.Val)).enc ++ A ∧
        s'.stk 1 = HvdH.encs (ys.reverse ++ arr) ++ Work.Layout.gMark :: B ∧
        s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
        s'.reg rFlatIn = HvdH.Glyph.eos := by
  intro ys
  induction ys with
  | nil =>
      intro arr A B g X hg h2 h1
      obtain ⟨s', n, hev, hn, h2', h1', h3', h4', hr'⟩ :=
        flattenInnerLoop_stop (main := main) (g := g) (X := X) (A := A) h2
      have hcost : n + 1 ≤ scanCost ([] : List Val) := by
        simp only [scanCost, List.map_nil, List.sum_nil]
        omega
      refine ⟨s', loopRuns.mono (k := 1) le_rfl (loopRuns.one hg hev) hcost, ?_, ?_, h3', h4', hr'⟩
      · rw [h2', h2]
      · simpa [h1'] using h1
  | cons y ys ih =>
      intro arr A B g X hg h2 h1
      obtain ⟨s₁, n₁, hev₁, hn₁, h2₁, h1₁, h3₁, h4₁, hr₁⟩ :=
        flattenInnerLoop_cons (main := main) (g := g) (X := X) (y := y) (ys := ys) (arr := arr)
          (A := A) (B := B) h2 h1
      obtain ⟨s₂, hrun₂, h2₂, h1₂, h3₂, h4₂, hr₂⟩ :=
        ih (y :: arr) A B s₁.reg s₁.stk hr₁ h2₁ h1₁
      have hcost : (n₁ + 1) + scanCost ys ≤ scanCost (y :: ys) := by
        simp only [scanCost, List.map_cons, List.sum_cons]
        omega
      have hcat := loopRuns.concat (ys.length + 1) (loopRuns.one hg hev₁) hrun₂
      have hcat1 : loopRuns main rFlatIn Glyph.cons flatInnerBody ((y :: ys).length + 1)
          ⟨g, X⟩ s₂ (n₁ + 1 + scanCost ys) :=
        loopRuns.cast (by simp only [List.length_cons]; omega) hcat
      have hcat2 : loopRuns main rFlatIn Glyph.cons flatInnerBody ((y :: ys).length + 1)
          ⟨g, X⟩ s₂ (scanCost (y :: ys)) :=
        loopRuns.mono (by simp only [List.length_cons]; omega) hcat1 hcost
      have hrev : ys.reverse ++ (y :: arr) = (y :: ys).reverse ++ arr := by
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      refine ⟨s₂, hcat2, h2₂, ?_, ?_, ?_, hr₂⟩
      · rw [h1₂, hrev]
      · rw [h3₂, h3₁]
      · rw [h4₂, h4₁]



/-!
# `Layout.flattenWord`

The list word of `LayoutLib.flatten`, built on `flattenProg` (definitions and cost
functions in `Submission/Work/Layout/flattenDefs.lean`): stack 0 holds `ofList (xss.map ofList)` and
receives `ofList xss.flatten`, at cost `O(vsz (ofList (xss.map ofList)))`.

This file contains

* the arithmetic bound `flattenCost` for the cost functions of the three phases;
* `flattenFoldLoop` (the third phase) and `flattenOuterLoop` (the first phase, which calls
  `flattenInnerLoop` from `flattenInnerLoop.lean` for its inner loop);
* the assembly of `flattenWord`.
-/

set_option autoImplicit false


open HvdH

/-! ## 1. Arithmetic: the cost bound -/

/-- The empty list of values encodes as the empty glyph list. -/
theorem encs_nil_eq : encs ([] : List Val) = [] := by simp [encs]

/-- `(l.map (fun x => f x + c)).sum = (l.map f).sum + c * l.length`. -/
theorem sum_map_add_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun x => f x + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Weight of a list of values: `vsz (ofList l) = W l + 1`. -/
def W (l : List Val) : ℕ := (l.map (fun y => vsz y + 1)).sum

theorem W_append (l₁ l₂ : List Val) : W (l₁ ++ l₂) = W l₁ + W l₂ := by
  simp [W, List.map_append, List.sum_append]

/-- Sums of sums are sums over the flattened list. -/
theorem sum_map_sum_flatten (xss : List (List Val)) :
    (xss.flatten.map (fun y => vsz y + 1)).sum
      = (xss.map (fun l => (l.map (fun y => vsz y + 1)).sum)).sum := by
  induction xss with
  | nil => rfl
  | cons l xss ih =>
      rw [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem W_flatten (xss : List (List Val)) : W xss.flatten = (xss.map W).sum :=
  sum_map_sum_flatten xss

/-- `vsz` of an `ofList` in terms of the weight. -/
theorem vsz_ofList_eq_W (l : List Val) : vsz (ofList l) = W l + 1 := by
  show vsz (ofList l) = (l.map (fun y => vsz y + 1)).sum + 1
  induction l with
  | nil => rfl
  | cons y ys ih =>
      have h : vsz (ofList (y :: ys)) = vsz y + vsz (ofList ys) + 1 := by
        show (Val.enc (ofList (y :: ys))).length = _
        rw [show ofList (y :: ys) = Val.cons y (ofList ys) from rfl]
        simp [vsz, Val.enc, List.length_append]
      rw [h, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem W_map_length_le (l : List Val) : l.length ≤ W l := by
  show l.length ≤ (l.map (fun y => vsz y + 1)).sum
  induction l with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem scanCost_eq (l : List Val) : scanCost l = 16 * W l + 5 * l.length + 4 := by
  show (l.map (fun y => 16 * (vsz y + 1) + 5)).sum + 4 = 16 * W l + 5 * l.length + 4
  rw [sum_map_add_const l (fun y => 16 * (vsz y + 1)) 5,
    List.sum_map_mul_left l (fun y => vsz y + 1) 16]
  rfl

theorem foldCost_eq (l : List Val) : foldCost l = 16 * W l + 6 * l.length + 4 := by
  show (l.map (fun y => 16 * (vsz y + 1) + 6)).sum + 4 = 16 * W l + 6 * l.length + 4
  rw [sum_map_add_const l (fun y => 16 * (vsz y + 1)) 6,
    List.sum_map_mul_left l (fun y => vsz y + 1) 16]
  rfl

theorem scanCost_cons (y : Val) (ys : List Val) :
    scanCost (y :: ys) = (16 * (vsz y + 1) + 5) + scanCost ys := by
  simp only [scanCost, List.map_cons, List.sum_cons]; ring

theorem scanCost_nil : scanCost ([] : List Val) = 4 := by simp [scanCost]

theorem foldCost_cons (y : Val) (ys : List Val) :
    foldCost (y :: ys) = (16 * (vsz y + 1) + 6) + foldCost ys := by
  simp only [foldCost, List.map_cons, List.sum_cons]; ring

theorem foldCost_nil : foldCost ([] : List Val) = 4 := by simp [foldCost]

theorem outerIterCost_eq (l : List Val) : outerIterCost l + 1 = 32 * W l + 5 * l.length + 45 := by
  have h1 := vsz_ofList_eq_W l
  have h2 := scanCost_eq l
  simp only [outerIterCost]
  omega

theorem outerCost_cons (l : List Val) (xss : List (List Val)) :
    outerCost (l :: xss) = (outerIterCost l + 1) + outerCost xss := by
  simp only [outerCost, List.map_cons, List.sum_cons]
  ring

theorem outerCost_eq (xss : List (List Val)) :
    outerCost xss = 32 * W xss.flatten + 5 * xss.flatten.length + 45 * xss.length + 4 := by
  induction xss with
  | nil => simp [outerCost, W]
  | cons l xss ih =>
      rw [outerCost_cons, ih, List.flatten_cons, W_append, List.length_append, List.length_cons]
      have hstep := outerIterCost_eq l
      omega

theorem W_map_ofList (xss : List (List Val)) :
    W (xss.map ofList) = W xss.flatten + 2 * xss.length := by
  have hfun : (fun y : Val => vsz y + 1) ∘ ofList = (fun l : List Val => W l + 2) := by
    funext l
    rw [Function.comp_apply, vsz_ofList_eq_W]
  have hL : W (xss.map ofList) = (xss.map (fun l : List Val => W l + 2)).sum := by
    show ((xss.map ofList).map (fun y : Val => vsz y + 1)).sum = _
    rw [List.map_map, hfun]
  rw [hL, sum_map_add_const xss (fun l => W l) 2, W_flatten]

/-- **The cost bound of the flatten word.** -/
theorem flattenCost (xss : List (List Val)) :
    outerCost xss + foldCost xss.flatten.reverse + 16 * (vsz (ofList xss.flatten) + 1) + 10
      ≤ 200 * (vsz (ofList (xss.map ofList)) + 1) := by
  have hout := outerCost_eq xss
  have hfold : foldCost xss.flatten.reverse = 16 * W xss.flatten + 6 * xss.flatten.length + 4 := by
    have h1 : foldCost xss.flatten.reverse
        = 16 * W (xss.flatten.reverse) + 6 * (xss.flatten.reverse).length + 4 := foldCost_eq _
    have h2 : W (xss.flatten.reverse) = W xss.flatten := by
      show (xss.flatten.reverse.map (fun y => vsz y + 1)).sum
        = (xss.flatten.map (fun y => vsz y + 1)).sum
      simp [List.map_reverse, List.sum_reverse]
    have h3 : (xss.flatten.reverse).length = xss.flatten.length := List.length_reverse
    rw [h1, h2, h3]
  have hsz : vsz (ofList xss.flatten) + 1 = W xss.flatten + 2 := by
    rw [vsz_ofList_eq_W]
  have hsl : vsz (ofList (xss.map ofList)) + 1 = W xss.flatten + 2 * xss.length + 2 := by
    rw [vsz_ofList_eq_W (xss.map ofList), W_map_ofList]
  have hle : xss.flatten.length ≤ W xss.flatten := W_map_length_le _
  rw [hout, hfold, hsz, hsl]
  omega

/-! ## 2. The fold loop (third phase) -/

/-- the collected elements are exhausted (stack 1 carries the sentinel `gMark`): stop. -/
theorem flatFoldBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {C : List Glyph} (h1 : X 1 = gMark :: C) :
    ∃ s' n, Ev main flatFoldBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 1 = X 1 ∧ s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFlatFold = Glyph.eos := by
  have hhead : (X 1).headD Glyph.eos = gMark := by rw [h1]; rfl
  have hpeek : Ev main (.peek 1 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ 1 := ev_peek' (main := main) 1 rA g X
  have hreg : (⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ : State).reg rA = gMark := by
    show Function.update g rA ((X 1).headD Glyph.eos) rA = gMark
    rw [Function.update_self, hhead]
  have hite : Ev main (.ite rA gMark (.set rFlatFold Glyph.eos)
      (.seq (mvVal 1 2 3 4) (.seq (pushConst 2 Glyph.cons) (.set rFlatFold gMark))))
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rFlatFold Glyph.eos, X⟩ 2 :=
    Ev.iteT hreg (ev_set' (main := main) rFlatFold Glyph.eos _ X)
  have hbody : Ev main flatFoldBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rFlatFold Glyph.eos, X⟩ 3 := by
    unfold flatFoldBody
    exact Ev.seq hpeek hite
  exact ⟨_, _, hbody, by omega, rfl, rfl, rfl, rfl, by simp⟩

/-- one element is left: move the value on top of stack 1 to stack 2 and push a `cons` glyph. -/
theorem flatFoldBody_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {y : Val} {ys acc : List Val} {C D : List Glyph}
    (h1 : X 1 = encs (y :: ys) ++ gMark :: C) (h2 : X 2 = (ofList acc).enc ++ D) :
    ∃ s' n, Ev main flatFoldBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz y + 1) + 5 ∧
      s'.stk 1 = encs ys ++ gMark :: C ∧ s'.stk 2 = (ofList (y :: acc)).enc ++ D ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFlatFold = gMark := by
  have hsplit : X 1 = y.enc ++ (encs ys ++ gMark :: C) := by
    rw [h1, encs_cons', List.append_assoc]
  have hhead : (X 1).headD Glyph.eos ≠ gMark := by
    rw [hsplit]; exact headD_enc_append_ne_gMark y _
  have hpeek : Ev main (.peek 1 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ 1 := ev_peek' (main := main) 1 rA g X
  obtain ⟨s₃, n₃, hmv, hn₃, h3a, h3b, h3c, h3d, h3o⟩ :=
    mvVal_ev_full (main := main) (a := 1) (b := 2) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update g rA ((X 1).headD Glyph.eos)) (X := X) (v := y)
      (A := encs ys ++ gMark :: C) (B := (ofList acc).enc ++ D) hsplit h2
  obtain ⟨s₄, n₄, hpc, hn₄, h4a, h4o, -, -⟩ :=
    pushConst_ev (main := main) (k := 2) (cst := Glyph.cons) (g := s₃.reg) (X := s₃.stk)
  have h4a' : s₄.stk 2 = (ofList (y :: acc)).enc ++ D := by
    rw [h4a, h3b, ofList_enc_cons, List.cons_append, List.append_assoc]
  have h4₁ : s₄.stk 1 = encs ys ++ gMark :: C := by rw [h4o 1 (by decide)]; exact h3a
  have h4₃ : s₄.stk 3 = X 3 := by rw [h4o 3 (by decide)]; exact h3c
  have h4₄ : s₄.stk 4 = X 4 := by rw [h4o 4 (by decide)]; exact h3d
  have hset : Ev main (.set rFlatFold gMark) s₄
      ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ 1 :=
    ev_set' (main := main) rFlatFold gMark s₄.reg s₄.stk
  have hreg : (⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ : State).reg rA ≠ gMark := by
    show ¬(Function.update g rA ((X 1).headD Glyph.eos) rA = gMark)
    rw [Function.update_self]
    exact hhead
  have hite : Ev main (.ite rA gMark (.set rFlatFold Glyph.eos)
      (.seq (mvVal 1 2 3 4) (.seq (pushConst 2 Glyph.cons) (.set rFlatFold gMark))))
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩
      ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ ((n₃ + (n₄ + 1)) + 1) :=
    Ev.iteF hreg (Ev.seq hmv (Ev.seq hpc hset))
  have hbody : Ev main flatFoldBody ⟨g, X⟩
      ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ (1 + ((n₃ + (n₄ + 1)) + 1)) := by
    unfold flatFoldBody
    exact Ev.seq hpeek hite
  have hn : 1 + ((n₃ + (n₄ + 1)) + 1) ≤ 16 * (vsz y + 1) + 5 := by omega
  obtain ⟨n, hev, hle⟩ := hbody.mono hn
  exact ⟨_, 16 * (vsz y + 1) + 5, ⟨n, hev, hle⟩, le_rfl, h4₁, h4a', h4₃, h4₄, by simp⟩

theorem flattenFoldLoop {main : Cmd} :
    ∀ (ys : List Val) (acc : List Val) (C D : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      g rFlatFold = gMark →
      X 1 = encs ys ++ gMark :: C →
      X 2 = (ofList acc).enc ++ D →
      ∃ s', loopRuns main rFlatFold gMark flatFoldBody (ys.length + 1) ⟨g, X⟩ s'
          (foldCost ys) ∧
        s'.stk 1 = gMark :: C ∧
        s'.stk 2 = (ofList (ys.reverse ++ acc)).enc ++ D ∧
        s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
        s'.reg rFlatFold = Glyph.eos := by
  intro ys
  induction ys with
  | nil =>
      intro acc C D g X hg h1 h2
      obtain ⟨s', n, hev, hn, h1', h2', h3', h4', hr'⟩ :=
        flatFoldBody_stop (main := main) (g := g) (X := X) h1
      have hcost : n + 1 ≤ foldCost ([] : List Val) := by
        rw [foldCost_nil]; omega
      refine ⟨s', loopRuns.mono (k := 1) le_rfl (loopRuns.one hg hev) hcost, ?_, ?_, h3', h4', hr'⟩
      · rw [h1', h1, encs_nil_eq, List.nil_append]
      · rw [h2', h2]
        simp
  | cons y ys ih =>
      intro acc C D g X hg h1 h2
      obtain ⟨s₁, n₁, hev₁, hn₁, h1₁, h2₁, h3₁, h4₁, hr₁⟩ :=
        flatFoldBody_cons (main := main) (g := g) (X := X) (y := y) (ys := ys) (acc := acc)
          (C := C) (D := D) h1 h2
      obtain ⟨s₂, hrun₂, h1₂, h2₂, h3₂, h4₂, hr₂⟩ :=
        ih (y :: acc) C D s₁.reg s₁.stk hr₁ h1₁ h2₁
      have hcost : (n₁ + 1) + foldCost ys ≤ foldCost (y :: ys) := by
        rw [foldCost_cons]; omega
      have hcat := loopRuns.concat (ys.length + 1) (loopRuns.one hg hev₁) hrun₂
      have hcat' : loopRuns main rFlatFold gMark flatFoldBody ((y :: ys).length + 1)
          ⟨g, X⟩ s₂ (foldCost (y :: ys)) :=
        loopRuns.mono (k := (y :: ys).length + 1) (by simp)
          (loopRuns.cast (by simp only [List.length_cons]; omega) hcat) hcost
      refine ⟨s₂, hcat', h1₂, ?_, by rw [h3₂, h3₁], by rw [h4₂, h4₁], hr₂⟩
      rw [h2₂, List.reverse_cons, List.append_assoc, List.singleton_append]

/-! ## 3. The outer loop (first phase) -/

/-- the outer list is exhausted (its encoding starts with `nil`): stop. -/
theorem flatOuterBody_nil {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {A₀ : List Glyph} (h0 : X 0 = (ofList ([] : List Val)).enc ++ A₀) :
    ∃ s' n, Ev main flatOuterBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 0 = X 0 ∧ s'.stk 1 = X 1 ∧ s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFlatOut = Glyph.eos := by
  have hhead : (X 0).headD Glyph.eos = Glyph.nil := by rw [h0]; rfl
  have hpeek : Ev main (.peek 0 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 0).headD Glyph.eos), X⟩ 1 := ev_peek' (main := main) 0 rA g X
  have hreg : (⟨Function.update g rA ((X 0).headD Glyph.eos), X⟩ : State).reg rA = Glyph.nil := by
    show Function.update g rA ((X 0).headD Glyph.eos) rA = Glyph.nil
    rw [Function.update_self, hhead]
  have hite : Ev main (.ite rA Glyph.nil (.set rFlatOut Glyph.eos)
      (.seq (.pop 0 rB) (.seq (mvVal 0 2 3 4) (.seq (.set rFlatIn Glyph.cons)
        (.seq (.loop rFlatIn Glyph.cons flatInnerBody) (.seq (.pop 2 rA) (.set rFlatOut Glyph.cons)))))))
      ⟨Function.update g rA ((X 0).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 0).headD Glyph.eos)) rFlatOut Glyph.eos, X⟩ 2 :=
    Ev.iteT hreg (ev_set' (main := main) rFlatOut Glyph.eos _ X)
  have hbody : Ev main flatOuterBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X 0).headD Glyph.eos)) rFlatOut Glyph.eos, X⟩ 3 := by
    unfold flatOuterBody
    exact Ev.seq hpeek hite
  exact ⟨_, _, hbody, by omega, rfl, rfl, rfl, rfl, rfl, by simp⟩

/-- one cell of the outer list: move the inner list value to stack 2, flatten it onto stack 1. -/
theorem flatOuterBody_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {l : List Val} {xss : List (List Val)} {arr : List Val} {A₀ B₁ C₂ : List Glyph}
    (h0 : X 0 = (ofList ((l :: xss).map ofList)).enc ++ A₀)
    (h1 : X 1 = encs arr ++ gMark :: B₁) (h2 : X 2 = C₂) :
    ∃ s' n, Ev main flatOuterBody ⟨g, X⟩ s' n ∧ n ≤ outerIterCost l ∧
      s'.stk 0 = (ofList (xss.map ofList)).enc ++ A₀ ∧
      s'.stk 1 = encs (l.reverse ++ arr) ++ gMark :: B₁ ∧
      s'.stk 2 = C₂ ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFlatOut = Glyph.cons := by
  have hsplit : X 0 = Glyph.cons :: ((ofList l).enc ++ ((ofList (xss.map ofList)).enc ++ A₀)) := by
    rw [h0, show (l :: xss).map ofList = ofList l :: xss.map ofList from rfl,
      ofList_enc_cons_append]
  have hhead : (X 0).headD Glyph.eos = Glyph.cons := by rw [hsplit]; rfl
  have htail : (X 0).tail = (ofList l).enc ++ ((ofList (xss.map ofList)).enc ++ A₀) := by
    rw [hsplit]; rfl
  have hpeek : Ev main (.peek 0 rA) ⟨g, X⟩
      ⟨Function.update g rA Glyph.cons, X⟩ 1 := by
    have h := ev_peek' (main := main) 0 rA g X
    rwa [hhead] at h
  have hpop : Ev main (.pop 0 rB) ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update g rA Glyph.cons) rB Glyph.cons,
        Function.update X 0 (X 0).tail⟩ 1 := by
    have h := ev_pop' (main := main) 0 rB (Function.update g rA Glyph.cons) X
    rwa [hhead] at h
  obtain ⟨s₃, n₃, hmv, hn₃, h3a, h3b, h3c, h3d, h3o⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 2) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update (Function.update g rA Glyph.cons) rB Glyph.cons)
      (X := Function.update X 0 (X 0).tail) (v := ofList l)
      (A := (ofList (xss.map ofList)).enc ++ A₀) (B := C₂)
      (by simp only [stkFn_same, htail])
      (by simp only [stkFn_ne X (by decide : (2 : Stk) ≠ 0), h2])
  have h3_1 : s₃.stk 1 = encs arr ++ gMark :: B₁ := by
    rw [h3o 1 (by decide) (by decide) (by decide) (by decide),
      stkFn_ne X (by decide : (1 : Stk) ≠ 0)]
    exact h1
  have h3_3 : s₃.stk 3 = X 3 := by
    rw [h3c, stkFn_ne X (by decide : (3 : Stk) ≠ 0)]
  have h3_4 : s₃.stk 4 = X 4 := by
    rw [h3d, stkFn_ne X (by decide : (4 : Stk) ≠ 0)]
  have hset : Ev main (.set rFlatIn Glyph.cons) s₃
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' (main := main) rFlatIn Glyph.cons s₃.reg s₃.stk
  obtain ⟨s₄, hrun₄, h4a, h4b, h4c, h4d, h4r⟩ :=
    flattenInnerLoop (main := main) l arr C₂ B₁
      (Function.update s₃.reg rFlatIn Glyph.cons) s₃.stk (by simp) h3b h3_1
  have hloop : Ev main (.loop rFlatIn Glyph.cons flatInnerBody)
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩ s₄ (scanCost l + 1) :=
    loopRuns.eval hrun₄ (by rw [h4r]; decide)
  have h4_0 : s₄.stk 0 = s₃.stk 0 :=
    Ev.frame hloop (S := ({1, 2, 3, 4} : Finset Stk)) (by decide) (by decide)
  have hpop2 : Ev main (.pop 2 rA) s₄
      ⟨Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos),
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩ 1 :=
    ev_pop' (main := main) 2 rA s₄.reg s₄.stk
  have htail2 : (s₄.stk 2).tail = C₂ := by rw [h4a]; rfl
  have hset2 : Ev main (.set rFlatOut Glyph.cons)
      ⟨Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos),
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩
      ⟨Function.update (Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos)) rFlatOut Glyph.cons,
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩ 1 :=
    ev_set' (main := main) rFlatOut Glyph.cons _ _
  have hbranch : Ev main (.seq (.pop 0 rB)
      (.seq (mvVal 0 2 3 4) (.seq (.set rFlatIn Glyph.cons)
        (.seq (.loop rFlatIn Glyph.cons flatInnerBody)
          (.seq (.pop 2 rA) (.set rFlatOut Glyph.cons))))))
      ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos)) rFlatOut Glyph.cons,
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩
      (1 + (n₃ + (1 + ((scanCost l + 1) + (1 + 1))))) :=
    Ev.seq hpop (Ev.seq hmv (Ev.seq hset (Ev.seq hloop (Ev.seq hpop2 hset2))))
  have hite : Ev main (.ite rA Glyph.nil (.set rFlatOut Glyph.eos)
      (.seq (.pop 0 rB) (.seq (mvVal 0 2 3 4) (.seq (.set rFlatIn Glyph.cons)
        (.seq (.loop rFlatIn Glyph.cons flatInnerBody)
          (.seq (.pop 2 rA) (.set rFlatOut Glyph.cons)))))))
      ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos)) rFlatOut Glyph.cons,
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩
      ((1 + (n₃ + (1 + ((scanCost l + 1) + (1 + 1))))) + 1) :=
    Ev.iteF (by simp) hbranch
  have hbody : Ev main flatOuterBody ⟨g, X⟩
      ⟨Function.update (Function.update s₄.reg rA ((s₄.stk 2).headD Glyph.eos)) rFlatOut Glyph.cons,
        Function.update s₄.stk 2 (s₄.stk 2).tail⟩
      (1 + ((1 + (n₃ + (1 + ((scanCost l + 1) + (1 + 1))))) + 1)) := by
    unfold flatOuterBody
    exact Ev.seq hpeek hite
  have hn : 1 + ((1 + (n₃ + (1 + ((scanCost l + 1) + (1 + 1))))) + 1) ≤ outerIterCost l := by
    have h := hn₃
    simp only [outerIterCost]
    omega
  obtain ⟨n, hev, hle⟩ := hbody.mono hn
  have hfin₀ : (Function.update s₄.stk 2 (s₄.stk 2).tail) 0
      = (ofList (xss.map ofList)).enc ++ A₀ := by
    rw [stkFn_ne s₄.stk (by decide : (0 : Stk) ≠ 2) (s₄.stk 2).tail, h4_0]
    exact h3a
  have hfin₁ : (Function.update s₄.stk 2 (s₄.stk 2).tail) 1
      = encs (l.reverse ++ arr) ++ gMark :: B₁ := by
    rw [stkFn_ne s₄.stk (by decide : (1 : Stk) ≠ 2) (s₄.stk 2).tail]; exact h4b
  have hfin₂ : (Function.update s₄.stk 2 (s₄.stk 2).tail) 2 = C₂ := by
    rw [stkFn_same]; exact htail2
  have hfin₃ : (Function.update s₄.stk 2 (s₄.stk 2).tail) 3 = X 3 := by
    rw [stkFn_ne s₄.stk (by decide : (3 : Stk) ≠ 2) (s₄.stk 2).tail, h4c]; exact h3_3
  have hfin₄ : (Function.update s₄.stk 2 (s₄.stk 2).tail) 4 = X 4 := by
    rw [stkFn_ne s₄.stk (by decide : (4 : Stk) ≠ 2) (s₄.stk 2).tail, h4d]; exact h3_4
  exact ⟨_, outerIterCost l, ⟨n, hev, hle⟩, le_rfl, hfin₀, hfin₁, hfin₂, hfin₃, hfin₄, by simp⟩

theorem flattenOuterLoop {main : Cmd} :
    ∀ (xss : List (List Val)) (arr : List Val) (A₀ B₁ C₂ C₃ C₄ : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      g rFlatOut = Glyph.cons →
      X 0 = (ofList (xss.map ofList)).enc ++ A₀ →
      X 1 = encs arr ++ gMark :: B₁ →
      X 2 = C₂ → X 3 = C₃ → X 4 = C₄ →
      ∃ s', loopRuns main rFlatOut Glyph.cons flatOuterBody (xss.length + 1) ⟨g, X⟩ s'
          (outerCost xss) ∧
        s'.stk 0 = (ofList ([] : List Val)).enc ++ A₀ ∧
        s'.stk 1 = encs (xss.flatten.reverse ++ arr) ++ gMark :: B₁ ∧
        s'.stk 2 = C₂ ∧ s'.stk 3 = C₃ ∧ s'.stk 4 = C₄ ∧
        s'.reg rFlatOut = Glyph.eos := by
  intro xss
  induction xss with
  | nil =>
      intro arr A₀ B₁ C₂ C₃ C₄ g X hg h0 h1 h2 h3 h4
      obtain ⟨s', n, hev, hn, h0', h1', h2', h3', h4', hr'⟩ :=
        flatOuterBody_nil (main := main) (g := g) (X := X) h0
      have hcost : n + 1 ≤ outerCost ([] : List (List Val)) := by
        simp only [outerCost, List.map_nil, List.sum_nil]
        omega
      refine ⟨s', loopRuns.mono (k := 1) le_rfl (loopRuns.one hg hev) hcost, ?_, ?_, ?_, ?_, ?_,
        hr'⟩
      · rw [h0', h0]; simp
      · rw [h1', h1]; simp
      · rw [h2', h2]
      · rw [h3', h3]
      · rw [h4', h4]
  | cons l xss ih =>
      intro arr A₀ B₁ C₂ C₃ C₄ g X hg h0 h1 h2 h3 h4
      obtain ⟨s₁, n₁, hev₁, hn₁, h0₁, h1₁, h2₁, h3₁, h4₁, hr₁⟩ :=
        flatOuterBody_cons (main := main) (g := g) (X := X) (l := l) (xss := xss) (arr := arr)
          (A₀ := A₀) (B₁ := B₁) (C₂ := C₂) h0 h1 h2
      obtain ⟨s₂, hrun₂, h0₂, h1₂, h2₂, h3₂, h4₂, hr₂⟩ :=
        ih (l.reverse ++ arr) A₀ B₁ C₂ C₃ C₄ s₁.reg s₁.stk hr₁ h0₁ h1₁ h2₁
          (by rw [h3₁, h3]) (by rw [h4₁, h4])
      have hcost : n₁ + 1 + outerCost xss ≤ outerCost (l :: xss) := by
        have h := outerCost_cons l xss
        omega
      have hcat := loopRuns.concat (xss.length + 1) (loopRuns.one hg hev₁) hrun₂
      refine ⟨s₂, loopRuns.mono (k := (l :: xss).length + 1) (by simp)
        (loopRuns.cast (by simp only [List.length_cons]; omega) hcat) hcost, ?_, ?_, h2₂, h3₂, h4₂, hr₂⟩
      · rw [h0₂]
      · rw [h1₂, List.flatten_cons, List.reverse_append, List.append_assoc]

/-! ## 4. The word -/

/-- **`LayoutLib.flatten`**: for each element `ofList l` of the outer list, move the elements of `l`
in order onto an output scratch stack (via `Work.Layout.mvVal` after popping the leading `cons`), then
rebuild the concatenated list.  Every glyph of `ofList (xss.map ofList)` is touched O(1) times. -/
theorem axFlattenWord : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xss : List (List Val)), WordR main p
    (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
    (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
    (fun _ => K * (vsz (ofList (xss.map ofList)) + 1)) := by
  refine ⟨flattenProg, 200, ?_⟩
  intro main xss vs hpre s R hs
  obtain ⟨rest, rfl⟩ := hpre
  have hs0 : s.stk 0 = (ofList (xss.map ofList)).enc ++ (encs rest ++ R) := by
    rw [hs, encs_cons', List.append_assoc]
  -- (1) sentinel at the bottom of the element stack
  obtain ⟨s₁, n₁, hpc₁, hn₁, h1a, h1o, -, -⟩ :=
    pushConst_ev (main := main) (k := 1) (cst := gMark) (g := s.reg) (X := s.stk)
  -- (2) enter the outer loop
  have hset₂ : Ev main (.set rFlatOut Glyph.cons) s₁
      ⟨Function.update s₁.reg rFlatOut Glyph.cons, s₁.stk⟩ 1 :=
    ev_set' (main := main) rFlatOut Glyph.cons s₁.reg s₁.stk
  -- (3) unpack the outer list and flatten it onto stack 1
  obtain ⟨s₂, hrun₂, h2a, h2b, h2c, h2d, h2e, h2r⟩ :=
    flattenOuterLoop (main := main) xss [] (encs rest ++ R) (s.stk 1) (s.stk 2) (s.stk 3) (s.stk 4)
      (Function.update s₁.reg rFlatOut Glyph.cons) s₁.stk (by simp)
      (by rw [h1o 0 (by decide)]; exact hs0)
      (by rw [h1a, encs_nil_eq, List.nil_append])
      (by rw [h1o 2 (by decide)])
      (by rw [h1o 3 (by decide)])
      (by rw [h1o 4 (by decide)])
  have hloop₂ : Ev main (.loop rFlatOut Glyph.cons flatOuterBody)
      ⟨Function.update s₁.reg rFlatOut Glyph.cons, s₁.stk⟩ s₂ (outerCost xss + 1) :=
    loopRuns.eval hrun₂ (by rw [h2r]; decide)
  -- (4) drop the final `nil` of the outer list
  have htail₀ : (s₂.stk 0).tail = encs rest ++ R := by rw [h2a]; rfl
  obtain ⟨s₃, hpop₀, hs₃₀, hs₃k⟩ :
      ∃ s₃, Ev main (.pop 0 rA) s₂ s₃ 1 ∧ s₃.stk 0 = encs rest ++ R ∧
        (∀ k, k ≠ 0 → s₃.stk k = s₂.stk k) := by
    refine ⟨_, ev_pop' (main := main) 0 rA s₂.reg s₂.stk, ?_, ?_⟩
    · show (Function.update s₂.stk 0 (s₂.stk 0).tail) 0 = encs rest ++ R
      rw [stkFn_same, htail₀]
    · intro k hk
      show (Function.update s₂.stk 0 (s₂.stk 0).tail) k = s₂.stk k
      rw [stkFn_ne s₂.stk hk (s₂.stk 0).tail]
  -- (5) accumulator `nil` on stack 2
  obtain ⟨s₄, n₄, hpc₄, hn₄, h4a, h4o, -, -⟩ :=
    pushConst_ev (main := main) (k := 2) (cst := Glyph.nil) (g := s₃.reg) (X := s₃.stk)
  -- (6) enter the fold loop
  have hset₅ : Ev main (.set rFlatFold gMark) s₄
      ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ 1 :=
    ev_set' (main := main) rFlatFold gMark s₄.reg s₄.stk
  have h4_1 : s₄.stk 1 = encs xss.flatten.reverse ++ gMark :: s.stk 1 := by
    rw [h4o 1 (by decide), hs₃k 1 (by decide), h2b, List.append_nil]
  have h4_2 : s₄.stk 2 = (ofList ([] : List Val)).enc ++ s.stk 2 := by
    rw [h4a, hs₃k 2 (by decide), h2c]
    rfl
  obtain ⟨s₆, hrun₆, h6a, h6b, h6c, h6d, h6r⟩ :=
    flattenFoldLoop (main := main) xss.flatten.reverse [] (s.stk 1) (s.stk 2)
      (Function.update s₄.reg rFlatFold gMark) s₄.stk (by simp) h4_1 h4_2
  have hloop₆ : Ev main (.loop rFlatFold gMark flatFoldBody)
      ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ s₆
      (foldCost xss.flatten.reverse + 1) :=
    loopRuns.eval hrun₆ (by rw [h6r]; decide)
  have h6_0 : s₆.stk 0 = s₄.stk 0 :=
    Ev.frame hloop₆ (S := ({1, 2, 3, 4} : Finset Stk)) (by decide) (by decide)
  -- (7) drop the sentinel
  have htail₁ : (s₆.stk 1).tail = s.stk 1 := by rw [h6a]; rfl
  obtain ⟨s₇, hpop₁, hs₇₁, hs₇k⟩ :
      ∃ s₇, Ev main (.pop 1 rA) s₆ s₇ 1 ∧ s₇.stk 1 = s.stk 1 ∧
        (∀ k, k ≠ 1 → s₇.stk k = s₆.stk k) := by
    refine ⟨_, ev_pop' (main := main) 1 rA s₆.reg s₆.stk, ?_, ?_⟩
    · show (Function.update s₆.stk 1 (s₆.stk 1).tail) 1 = s.stk 1
      rw [stkFn_same, htail₁]
    · intro k hk
      show (Function.update s₆.stk 1 (s₆.stk 1).tail) k = s₆.stk k
      rw [stkFn_ne s₆.stk hk (s₆.stk 1).tail]
  have h6b' : s₆.stk 2 = (ofList xss.flatten).enc ++ s.stk 2 := by
    rw [h6b, List.reverse_reverse, List.append_nil]
  -- (8) move the result back to stack 0
  obtain ⟨s₈, n₈, hmv₈, hn₈, h8a, h8b, h8c, h8d, h8o⟩ :=
    mvVal_ev_full (main := main) (a := 2) (b := 0) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₇.reg) (X := s₇.stk) (v := ofList xss.flatten) (A := s.stk 2) (B := encs rest ++ R)
      (by rw [hs₇k 2 (by decide), h6b'])
      (by rw [hs₇k 0 (by decide), h6_0, h4o 0 (by decide), hs₃₀])
  -- (9) assemble the run
  have hB1 : Ev main _ s₆ s₈ (1 + n₈) := Ev.seq hpop₁ hmv₈
  have hB2 : Ev main _ ⟨Function.update s₄.reg rFlatFold gMark, s₄.stk⟩ s₈
      ((foldCost xss.flatten.reverse + 1) + (1 + n₈)) :=
    Ev.seq hloop₆ hB1
  have hB3 : Ev main _ s₄ s₈ (1 + ((foldCost xss.flatten.reverse + 1) + (1 + n₈))) :=
    Ev.seq hset₅ hB2
  have hB4 : Ev main _ s₃ s₈ (n₄ + (1 + ((foldCost xss.flatten.reverse + 1) + (1 + n₈)))) :=
    Ev.seq hpc₄ hB3
  have hB5 : Ev main _ s₂ s₈ (1 + (n₄ + (1 + ((foldCost xss.flatten.reverse + 1) + (1 + n₈))))) :=
    Ev.seq hpop₀ hB4
  have hB6 : Ev main _ ⟨Function.update s₁.reg rFlatOut Glyph.cons, s₁.stk⟩ s₈
      ((outerCost xss + 1) + (1 + (n₄ + (1 + ((foldCost xss.flatten.reverse + 1) + (1 + n₈)))))) :=
    Ev.seq hloop₂ hB5
  have hB7 : Ev main _ s₁ s₈
      (1 + ((outerCost xss + 1) + (1 + (n₄ + (1 + ((foldCost xss.flatten.reverse + 1) + (1 + n₈))))))) :=
    Ev.seq hset₂ hB6
  have hpc₁' : Ev main (pushConst 1 gMark) s s₁ 2 := hpc₁.mono hn₁
  have hbody : Ev main flattenProg s s₈
      (2 + (1 + ((outerCost xss + 1) + (1 + (n₄ + (1 + ((foldCost xss.flatten.reverse + 1)
        + (1 + n₈)))))))) := by
    unfold flattenProg
    exact Ev.seq hpc₁' hB7
  have hfin : 2 + (1 + ((outerCost xss + 1) + (1 + (n₄ + (1 + ((foldCost xss.flatten.reverse + 1)
      + (1 + n₈))))))) ≤ 200 * (vsz (ofList (xss.map ofList)) + 1) := by
    have hfc := flattenCost xss
    have h4 := hn₄
    have h8 := hn₈
    omega
  obtain ⟨n, hev, hn⟩ := hbody.mono hfin
  have hres : s₈.stk 0 = encs (ofList xss.flatten :: rest) ++ R := by
    rw [h8b, encs_cons', List.append_assoc]
  refine ⟨ofList xss.flatten :: rest, s₈, n, ⟨rest, rfl, rfl⟩, hev, hn, hres, ?_⟩
  intro k hk
  by_cases h1 : k = 1
  · subst h1
    rw [h8o 1 (by decide) (by decide) (by decide) (by decide), hs₇₁]
  by_cases h2 : k = 2
  · subst h2
    exact h8a
  by_cases h3 : k = 3
  · subst h3
    rw [h8c, hs₇k 3 (by decide), h6c, h4o 3 (by decide), hs₃k 3 (by decide), h2d]
  by_cases h4 : k = 4
  · subst h4
    rw [h8d, hs₇k 4 (by decide), h6d, h4o 4 (by decide), hs₃k 4 (by decide), h2e]
  · exact Eval.stk_frame hev
      (by rw [cmdTouches_flattenProg]; exact notMem_01234 hk h1 h2 h3 h4)



end Work.SynFFT.AxFlat
