-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/chunksOfDefs.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBits_bits
/-!
# `LayoutLib.chunksOf`: raw StackLang program

Cut `ofList xs` (top of stack 0, below an integer `m`) into consecutive chunks of length `m`
(`1 ≤ m`, `m ∣ xs.length`).

Design (raw stack level):

* `readBitsProg` : pop the sign and the bits of the integer `m` from stack 0, leaving the bits
  (least significant first, reversed to most significant first) on `sBits`, above a sentinel
  `gMark`; the `iend` is dropped.  Cost `O(isz m)`.
* `buildCounterProg` : walk those bits (most significant first) building a unary counter
  `gPend^m ++ [gSent]` on `sM`, by repeated doubling (`doubleProg`).  Cost `O(m)`; only run when
  the list is non-empty (`m ≤ xs.length`).
* `walkProg` : walk the list on stack 0, moving every element to stack `sT` (so the *first*
  element ends up deepest, i.e. `sT` holds the reversed list above a sentinel).  Cost `O(vsz)`.
* `buildProg` : push `nil`, then repeatedly: push `nil`, copy the unary counter `sM` into `sW`,
  move `m` elements from `sT` to stack 0 pushing a `cons` after each, drop the counter sentinel
  of `sW`, push `cons`.  This builds `ofList chunks` on stack 0, chunk by chunk from the last one.
* cleanup: drop the sentinel of `sT`, drain `sM` down to its own sentinel.

Every program restores all stacks except stack 0.
-/

set_option autoImplicit false

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

/-! ## Scratch stacks, registers and markers -/

/-- element stack: holds the elements of the list (last element first), above a `gSent` sentinel -/
def sT : Stk := 1
/-- `mvVal` buffer -/
def sB : Stk := 2
/-- `mvVal` counter -/
def sC : Stk := 3
/-- master unary counter: `gPend^m ++ [gSent]` -/
def sM : Stk := 4
/-- working unary counter (copy of `sM`, consumed by the element loop) -/
def sW : Stk := 5
/-- bits of `m`, most significant first, above a `gMark` sentinel -/
def sBits : Stk := 6
/-- scratch stack of `doubleProg` -/
def sT2 : Stk := 7
/-- scratch stack holding the bit currently being processed by `buildCounterBody` -/
def sFl : Stk := 8

/-- scratch register -/
def rE : Reg := 5
/-- loop driver register of the counter-copy loop -/
def rF : Reg := 6
/-- loop driver register of the element loop -/
def rH : Reg := 7

/-- "continue" glyph of the loop drivers -/
def gCont : Glyph := .mk 10

/-! ## Programs -/

/-- `set rE c ;; push k rE` -/
def pushK (k : Stk) (c : Glyph) : Cmd := seqs [.set rE c, .push k rE]

/-- body of the bit-reading loop: pop a glyph of `(int m).enc`; `iend` stops the loop, other
glyphs (the bits) are pushed on `sBits` -/
def readBitBody : Cmd := seqs [.peek 0 rE,
  .ite rE Glyph.iend
    (seqs [.pop 0 rE, .set rLoopG Glyph.eos])
    (seqs [.pop 0 rE, .push sBits rE, .set rLoopG gCont])]

/-- read the bits of the integer on top of stack 0 onto `sBits` (most significant first), dropping
the sign and the `iend` -/
def readBitsProg : Cmd := seqs [.pop 0 rE, pushK sBits gMark, .set rLoopG gCont,
  .loop rLoopG gCont readBitBody]

/-- move every `gPend` of `sM` to `sT2`, stopping below the `gSent` sentinel -/
def doubMoveBody : Cmd := seqs [.peek sM rE,
  .ite rE gSent (.set rLoopG Glyph.eos)
    (seqs [.pop sM rE, .push sT2 rE, .set rLoopG gCont])]

/-- move every glyph of `sT2` back to `sM`, pushing it twice, stopping at the `gMark` sentinel -/
def doubDupBody : Cmd := seqs [.peek sT2 rE,
  .ite rE gMark (.set rLoopG Glyph.eos)
    (seqs [.pop sT2 rE, .push sM rE, .push sM rE, .set rLoopG gCont])]

/-- double the unary counter on `sM` (below its `gSent` sentinel) -/
def doubleProg : Cmd := seqs [pushK sT2 gMark,
  .set rLoopG gCont, .loop rLoopG gCont doubMoveBody,
  .set rLoopG gCont, .loop rLoopG gCont doubDupBody,
  .pop sT2 rE]

/-- body of the counter-building loop: pop a bit of `sBits` (stopping at `gMark`), double the
counter `sM` and add one if the bit is `true` -/
def buildCounterBody : Cmd := seqs [.peek sBits rE,
  .ite rE gMark (.set rLoopG Glyph.eos)
    (seqs [.pop sBits rE, .push sFl rE, doubleProg,
      .peek sFl rE, .ite rE (Glyph.bit true) (pushK sM gPend) .skip,
      .pop sFl rE, .set rLoopG gCont])]

/-- build the unary counter `gPend^m ++ [gSent]` on `sM` from the bits (most significant first) on
`sBits`; `sBits` is drained -/
def buildCounterProg : Cmd := seqs [pushK sM gSent, .set rLoopG gCont,
  .loop rLoopG gCont buildCounterBody, .pop sBits rE]

/-- body of the list-walking loop: on `cons`, drop the glyph and move the element to `sT`; on
`nil`, stop -/
def walkBody : Cmd := seqs [.peek 0 rE,
  .ite rE Glyph.cons
    (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont])
    (.set rLoopG Glyph.eos)]

/-- move every element of the list on stack 0 to `sT`, leaving `nil` on stack 0 -/
def walkProg : Cmd := seqs [pushK sT gSent, .set rLoopG gCont, .loop rLoopG gCont walkBody]

/-- body of the counter-copy loop: move one glyph of `sM` (below the `gSent` sentinel) to `sT2` -/
def cpyOutBody : Cmd := seqs [.peek sM rE,
  .ite rE gSent (.set rF Glyph.eos)
    (seqs [.pop sM rE, .push sT2 rE, .set rF gCont])]

/-- second half of the counter-copy loop: move one glyph of `sT2` back to `sM` and forward to
`sW` -/
def cpyBackBody : Cmd := seqs [.peek sT2 rE,
  .ite rE gMark (.set rF Glyph.eos)
    (seqs [.pop sT2 rE, .push sM rE, .push sW rE, .set rF gCont])]

/-- Copy the unary counter on `sM` (down to and including its `gSent` sentinel) to `sW`, restoring
`sM` (via the scratch stack `sT2`). -/
def copyProg : Cmd := seqs [pushK sT2 gMark,
  .set rF gCont, .loop rF gCont cpyOutBody,
  .pop sM rE, .push sT2 rE,
  .set rF gCont, .loop rF gCont cpyBackBody,
  .pop sT2 rE]

/-- body of the element loop: while the working counter `sW` is not at its sentinel, consume one
unit and move one element of `sT` to stack 0, pushing a `cons` -/
def elemBody : Cmd := seqs [.peek sW rE,
  .ite rE gSent (.set rH Glyph.eos)
    (seqs [.pop sW rE, mvVal sT 0 sB sC, pushK 0 Glyph.cons, .set rH gCont])]

/-- move `m` elements (the number of units of `sW`) from `sT` to stack 0 -/
def innerProg : Cmd := seqs [.set rH gCont, .loop rH gCont elemBody]

/-- one chunk: push the terminator `nil`, copy the counter, move `m` elements, push the outer
`cons` -/
def groupBody : Cmd := seqs [.peek sT rE,
  .ite rE gSent (.set rLoopG Glyph.eos)
    (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
      .set rLoopG gCont])]

/-- build `ofList chunks` on stack 0 from the elements on `sT`, chunk by chunk (last chunk first) -/
def buildProg : Cmd := seqs [pushK 0 Glyph.nil, .set rLoopG gCont,
  .loop rLoopG gCont groupBody]

/-- drain stack `k` down to and including the first occurrence of `κ` -/
def drainToBody (k : Stk) (κ : Glyph) : Cmd := seqs [.peek k rE,
  .ite rE κ (seqs [.pop k rE, .set rLoopG Glyph.eos])
             (seqs [.pop k rE, .set rLoopG gCont])]

/-- drain stack `k` down to and including the first occurrence of `κ` -/
def drainToProg (k : Stk) (κ : Glyph) : Cmd := seqs [.set rLoopG gCont,
  .loop rLoopG gCont (drainToBody k κ)]

/-- empty-list branch: drop the bits from `sBits` -/
def emptyProg : Cmd := drainToProg sBits gMark

/-- non-empty branch -/
def fullProg : Cmd := seqs [buildCounterProg, walkProg, .pop 0 rE, buildProg, .pop sT rE,
  drainToProg sM gSent]

/-- the whole `chunksOf` word -/
def mainProg : Cmd := seqs [readBitsProg, .peek 0 rE,
  .ite rE Glyph.cons fullProg emptyProg]

/-! ## Pure lists: encodings -/

/-- the glyphs of a bit list -/
def bitsG (l : List Bool) : List Glyph := l.map Glyph.bit

@[simp] theorem bitsG_nil : bitsG ([] : List Bool) = [] := rfl

theorem bitsG_append (a b : List Bool) : bitsG (a ++ b) = bitsG a ++ bitsG b := by
  simp [bitsG]

theorem bitsG_reverse (l : List Bool) : bitsG l.reverse = (bitsG l).reverse := by
  simp [bitsG]

@[simp] theorem bitsG_length (l : List Bool) : (bitsG l).length = l.length := by
  simp [bitsG]

theorem gMark_notMem_bitsG (l : List Bool) : gMark ∉ bitsG l := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact gMark_ne_bit b hb.symm

theorem gPend_notMem_bitsG (l : List Bool) : gPend ∉ bitsG l := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact gPend_ne_bit b hb.symm

theorem gSent_notMem_bitsG (l : List Bool) : gSent ∉ bitsG l := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact gSent_ne_bit b hb.symm

/-- the encoding of the integer `m` -/
theorem enc_int_nat (m : ℕ) :
    (Val.int (m : ℤ)).enc = Glyph.pos :: (bitsG m.bits ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
  simp [bitsG, Int.natAbs_natCast]

theorem enc_int_nat_length (m : ℕ) : (Val.int (m : ℤ)).enc.length = isz (m : ℤ) :=
  Work.IntLib.vsz_int (m : ℤ)

/-- the encoding of `ofList`: the `cons` of every element, then `nil` -/
theorem enc_ofList_eq (ys : List Val) :
    (ofList ys).enc = (ys.map fun v => Glyph.cons :: v.enc).flatten ++ [Glyph.nil] := by
  induction ys with
  | nil => rfl
  | cons v ys ih =>
      rw [show ofList (v :: ys) = Val.cons v (ofList ys) from rfl, Val.enc, List.map_cons,
        List.flatten_cons, ih]
      simp [List.cons_append, List.append_assoc]

@[simp] theorem enc_ofList_nil : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

theorem enc_ofList_cons (v : Val) (ys : List Val) :
    (ofList (v :: ys)).enc = Glyph.cons :: (v.enc ++ (ofList ys).enc) := rfl

/-- `vsz` of a list is at least its length -/
theorem length_le_vsz_ofList : ∀ ys : List Val, ys.length ≤ vsz (ofList ys)
  | [] => by simp [vsz, ofList, Val.enc]
  | v :: ys => by
      have ih := length_le_vsz_ofList ys
      have hv := one_le_vsz v
      rw [show ofList (v :: ys) = Val.cons v (ofList ys) from rfl]
      simp only [vsz, Val.enc, List.length_cons, List.length_append] at ih hv ⊢
      omega

/-- the head glyph of `ofList ys` -/
theorem headD_enc_ofList (ys : List Val) (d : Glyph) :
    ((ofList ys).enc).headD d = if ys = [] then Glyph.nil else Glyph.cons := by
  cases ys with
  | nil => simp [ofList, Val.enc]
  | cons v ys =>
      rw [show ofList (v :: ys) = Val.cons v (ofList ys) from rfl]
      simp [Val.enc]


/-! ## Pure lists: the bit fold `valBits` -/

/-- `valBits L c` folds the bits of `L` (most significant first) into the accumulator `c` -/
def valBits (L : List Bool) (c : ℕ) : ℕ := L.foldl (fun c b => 2 * c + b.toNat) c

@[simp] theorem valBits_nil (c : ℕ) : valBits [] c = c := rfl

theorem valBits_cons (b : Bool) (t : List Bool) (c : ℕ) :
    valBits (b :: t) c = valBits t (2 * c + b.toNat) := rfl

theorem valBits_append (a b : List Bool) (c : ℕ) :
    valBits (a ++ b) c = valBits b (valBits a c) := by
  simp only [valBits, List.foldl_append]

/-- the fold gives the bit value plus `2^{length}` times the accumulator -/
theorem valBits_eq (L : List Bool) (c : ℕ) :
    valBits L c = Work.IntLib.ofBits L.reverse + 2 ^ L.length * c := by
  induction L generalizing c with
  | nil => simp [valBits, Work.IntLib.ofBits]
  | cons b t ih =>
      rw [valBits_cons, ih, List.reverse_cons, Work.IntLib.ofBits_append]
      have hb : Work.IntLib.ofBits [b] = b.toNat := by simp [Work.IntLib.ofBits]
      rw [hb, List.length_cons, pow_succ, List.length_reverse]
      ring

theorem valBits_reverse_zero (L : List Bool) : valBits L.reverse 0 = Work.IntLib.ofBits L := by
  rw [valBits_eq]
  simp

theorem valBits_bits_reverse (m : ℕ) : valBits m.bits.reverse 0 = m := by
  rw [valBits_reverse_zero, Work.IntLib.ofBits_bits]

/-! ## Pure lists: chunk flattening -/

/-- an `l`-chunk of `m` elements starting at `i` -/
def chunkAt (m : ℕ) (xs : List Val) (i : ℕ) : List Val := (xs.drop (i * m)).take m

/-- the concatenation of the consecutive `m`-chunks is the whole list -/
theorem flatMap_range_chunkAt (m : ℕ) (xs : List Val) :
    ∀ k : ℕ, (List.range k).flatMap (fun i => chunkAt m xs i) = xs.take (k * m) := by
  intro k
  induction k with
  | zero => simp [chunkAt]
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_cons]
      simp only [chunkAt, List.flatMap_nil, List.append_nil]
      rw [← List.take_add]
      congr 1
      ring

/-- the concatenation of the consecutive `m`-chunks is the whole list -/
theorem flatMap_range_chunkAt_eq {m : ℕ} (xs : List Val) (hd : m ∣ xs.length) :
    (List.range (xs.length / m)).flatMap (fun i => chunkAt m xs i) = xs := by
  rw [flatMap_range_chunkAt, Nat.div_mul_cancel hd, List.take_length]

/-! ## Element push order -/

/-- the glyphs pushed on stack 0 by one group, before the elements are moved: the element loop
pushes `[cons, y_0, cons, y_1, ...]` (in stack order, top first) -/
def twist (ys : List Val) : List Glyph := (ys.reverse.map fun v => Glyph.cons :: v.enc).flatten

theorem twist_cons (y : Val) (ys : List Val) :
    twist (y :: ys) = twist ys ++ (Glyph.cons :: y.enc) := by
  simp only [twist, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.nil_append]
  rw [List.append_nil]

/-- the group block is exactly the encoding of the chunk -/
theorem twist_reverse_enc (ys : List Val) : twist ys.reverse ++ [Glyph.nil] = (ofList ys).enc := by
  rw [twist, List.reverse_reverse, enc_ofList_eq]

/-- the order in which the element stack `sT` delivers the elements of the chunks `ch`:
last chunk first, each chunk reversed -/
def elemOrder (ch : List (List Val)) : List Val := (ch.reverse).flatMap List.reverse

theorem elemOrder_concat_singleton (A : List (List Val)) (x : List Val) :
    elemOrder (A ++ [x]) = x.reverse ++ elemOrder A := by
  simp only [elemOrder, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem elemOrder_range_map (f : ℕ → List Val) :
    ∀ k : ℕ, elemOrder ((List.range k).map f) = ((List.range k).flatMap f).reverse := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have hsplit : (List.range (k + 1)).map f = (List.range k).map f ++ [f k] := by
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      have hsplit2 : (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
      rw [hsplit, hsplit2, List.reverse_append, elemOrder_concat_singleton, ih]

/-! ## Pure lists: bounding the intermediate counter values -/

/-- sum of the powers of two below `n` is at most `2^n` -/
theorem sum_two_pow_le : ∀ n : ℕ, ((List.range n).map (fun i => 2 ^ i)).sum ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append]
      have ih := sum_two_pow_le n
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.nil_append]
      have h : (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      omega

theorem sum_map_add (l : List ℕ) (f g : ℕ → ℕ) :
    (l.map (fun i => f i + g i)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_right (l : List ℕ) (f : ℕ → ℕ) (b : ℕ) :
    (l.map (fun i => f i * b)).sum = (l.map f).sum * b := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_congr {l : List ℕ} {f g : ℕ → ℕ} (h : ∀ i ∈ l, f i = g i) :
    (l.map f).sum = (l.map g).sum := by
  induction l generalizing f g with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (List.mem_cons_self ..),
        ih (f := f) (g := g) (fun i hi => h i (List.mem_cons_of_mem a hi))]

/-- the sum of the `valBits` of the prefixes of a bit list is at most the value of the list -/
theorem sum_valBits_take_le (L : List Bool) :
    ((List.range L.length).map (fun i => valBits (L.take i) 0)).sum ≤ valBits L 0 := by
  induction L with
  | nil => simp
  | cons b t ih =>
      have hlen : (b :: t).length = t.length + 1 := rfl
      have hsum : ((List.range (b :: t).length).map (fun i => valBits ((b :: t).take i) 0)).sum
          = ((List.range t.length).map (fun i => valBits (t.take i) b.toNat)).sum := by
        rw [hlen, List.range_succ_eq_map, List.map_cons, List.sum_cons]
        simp only [List.take_zero, valBits_nil, List.sum_nil, zero_add]
        rw [List.map_map]
        rw [sum_map_congr (l := List.range t.length)
          (f := (fun i => valBits ((b :: t).take i) 0) ∘ Nat.succ)
          (g := fun i => valBits (t.take i) b.toNat) (by
            intro i _
            rw [Function.comp_apply, List.take_succ_cons, valBits_cons]
            norm_num)]
      have hsplit : ((List.range t.length).map (fun i => valBits (t.take i) b.toNat)).sum
          = ((List.range t.length).map (fun i => valBits (t.take i) 0)).sum
            + b.toNat * ((List.range t.length).map (fun i => 2 ^ i)).sum := by
        have h1 : ∀ i ∈ List.range t.length,
            valBits (t.take i) b.toNat = valBits (t.take i) 0 + 2 ^ i * b.toNat := by
          intro i hi
          have hile : i ≤ t.length := le_of_lt (List.mem_range.mp hi)
          have hleni : (t.take i).length = i := by simp [List.length_take]; omega
          rw [valBits_eq, valBits_eq, hleni]
          ring
        rw [sum_map_congr h1, sum_map_add, sum_map_mul_right]
        ring
      rw [hsum, hsplit]
      have hle := sum_two_pow_le t.length
      have hval : valBits (b :: t) 0 = valBits t 0 + 2 ^ t.length * b.toNat := by
        rw [valBits_cons, valBits_eq, valBits_eq]
        ring
      have hb : b.toNat * ((List.range t.length).map (fun i => 2 ^ i)).sum
          ≤ 2 ^ t.length * b.toNat := by
        calc b.toNat * ((List.range t.length).map (fun i => 2 ^ i)).sum
            ≤ b.toNat * 2 ^ t.length := Nat.mul_le_mul_left _ hle
          _ = 2 ^ t.length * b.toNat := Nat.mul_comm _ _
      have hih := ih
      rw [hval]
      omega

/-- `vsz` of a nonempty `ofList` -/
theorem vsz_ofList_cons (y : Val) (ys : List Val) :
    vsz (ofList (y :: ys)) = vsz y + vsz (ofList ys) + 1 := by
  simp only [vsz, enc_ofList_cons, List.length_cons, List.length_append]

theorem iend_notMem_bitsG (l : List Bool) : Glyph.iend ∉ bitsG l := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact (fun e => by cases e) hb.symm

theorem gPend_ne_gSent : gPend ≠ gSent := fun h => gSent_ne_gPend h.symm
theorem gMark_ne_gPend : gMark ≠ gPend := by decide
theorem gPend_ne_gMark : gPend ≠ gMark := by decide
theorem gMark_ne_gSent : gMark ≠ gSent := by decide
theorem gSent_ne_gMark : gSent ≠ gMark := by decide
theorem gMark_ne_gCont : gMark ≠ gCont := by decide
theorem gSent_ne_gCont : gSent ≠ gCont := by decide
theorem gPend_ne_gCont : gPend ≠ gCont := by decide

theorem gMark_notMem_replicate (k : ℕ) : gMark ∉ List.replicate k gPend := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, gMark_ne_gPend, ih]

theorem gSent_notMem_replicate (k : ℕ) : gSent ∉ List.replicate k gPend := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, gSent_ne_gPend, ih]

/-- the sum of the intermediate counter values of `buildCounter` -/
def Ssum (L : List Bool) (c : ℕ) : ℕ := ((List.range L.length).map (fun i => valBits (L.take i) c)).sum

theorem Ssum_cons (b : Bool) (L : List Bool) (c : ℕ) :
    Ssum (b :: L) c = c + Ssum L (2 * c + b.toNat) := by
  have hlen : (b :: L).length = L.length + 1 := rfl
  unfold Ssum
  rw [hlen, List.range_succ_eq_map, List.map_cons, List.sum_cons]
  simp only [List.take_zero, valBits_nil, List.sum_nil, zero_add]
  rw [List.map_map]
  rw [sum_map_congr (l := List.range L.length)
    (f := (fun i => valBits ((b :: L).take i) c) ∘ Nat.succ)
    (g := fun i => valBits (L.take i) (2 * c + b.toNat)) (by
      intro i _
      rw [Function.comp_apply, List.take_succ_cons, valBits_cons])]

theorem Ssum_zero_le (L : List Bool) : Ssum L 0 ≤ valBits L 0 := by
  simpa [Ssum] using sum_valBits_take_le L

end Work.Resample.PBChunk