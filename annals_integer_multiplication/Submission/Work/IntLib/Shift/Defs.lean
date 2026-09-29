import Mathlib
import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.Defs

/-!
# `IntLib` / shift words: definitions

StackLang programs implementing the three shift words of `HvdH.IntLib`:

* `shlProg`:  `int a :: int k :: rest ↦ int (a * 2^k)`,     cost `O(isz a + k + isz k)`;
* `shrTProg`: `int a :: int k :: rest ↦ int (a.tdiv 2^k)`,  cost `O(isz a + isz k)`;
* `shrFProg`: `int a :: int k :: rest ↦ int (a.fdiv 2^k)`,  cost `O(isz a + isz k)`.

Encoding reminder: `(Val.int z).enc = [pos|neg] ++ (encodeNat |z|).map bit ++ [iend]`, first glyph
on top of stack 0, so the top value is `a` and the second one is `k`.

## Shape of the computation

* `parse` splits the two values: sign glyph of `a` in the region of `sSg`, bits of `|a|` least
  significant first in the region of `sM`, bits of `k` *most significant first* in the region of
  `sK`; stack 0 keeps the tail `rest`.
* the main loop (`shlLoop`/`shrLoop`) walks the bits of `k` from the most significant one down,
  maintaining a *block* region `sP` of `gUnit` glyphs whose length is the value of the bits
  processed so far (Horner `s ↦ 2s + b`).  Every unit of the block is one unit of work:
  - `shl`: push one `gZero` into the region of `sA`;
  - `shrT`/`shrF`: pop one bit of `|a|` from the region of `sM`, recording in `rD` whether a
    `true` bit was popped and setting `rE := gStop` when the bits of `|a|` run out.
  Since the block length doubles at every stage, the work is `O(k)` (`shl`) resp.
  `O(min k (size |a|))` (`shrT`/`shrF`), so in particular independent of `k` for the shift-rights.
* `incRgn` increases the magnitude region of `sM` by one (carry propagation); it is applied (as
  `incIf`) exactly when `a < 0` and a `true` bit was dropped, which turns the truncated quotient
  `|a| / 2^k` into the ceiling `⌈|a|/2^k⌉` needed by `Int.fdiv`.
* `finishShl`/`finishShr` rebuild the value encoding of the answer on stack 0, `cleanup` restores
  the scratch stacks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

/-! ## Flag glyphs, stacks, registers -/

/-- `rD` flag: some dropped bit was `true` -/
def gAny : Glyph := .mk 10
/-- `rD` flag: no dropped bit was `true` -/
def gNo : Glyph := .mk 11
/-- one unit of the block region -/
def gUnit : Glyph := .mk 12
/-- one zero written into the accumulator: the *actual* glyph of the answer encoding for a `false`
bit, so that the accumulator can be emitted directly -/
def gZero : Glyph := Glyph.bit false

theorem gAny_ne_gNo : gAny ≠ gNo := by decide
theorem gNo_ne_gAny : gNo ≠ gAny := by decide
theorem gAny_ne_gGo : gAny ≠ gGo := by decide
theorem gGo_ne_gAny : gGo ≠ gAny := by decide
theorem gAny_ne_gStop : gAny ≠ gStop := by decide

/-- sign glyph of `a` -/
def sSg : Stk := 1
/-- bits of `|a|`, least significant first -/
def sM : Stk := 2
/-- bits of `k`, most significant first -/
def sK : Stk := 3
/-- block region (clock) -/
def sP : Stk := 4
/-- accumulator region (`shl` only) -/
def sA : Stk := 5
/-- general temp -/
def sT : Stk := 6
/-- temp for the block doubling -/
def sT2 : Stk := 7

/-- outer loop flag register -/
def rO : Reg := 0
/-- inner (pass) loop flag register -/
def rI : Reg := 1
/-- drain/clear loop flag register -/
def rJ : Reg := 2
/-- "bits of `|a|` exhausted" flag register -/
def rE : Reg := 3
/-- "some dropped bit was true" flag register -/
def rD : Reg := 4
/-- scratch register -/
def rX : Reg := 5
/-- scratch register -/
def rY : Reg := 6
/-- scratch register -/
def rZ : Reg := 7
/-- scratch register holding the current bit of `k` -/
def rW : Reg := 8

/-! ## Elementary programs -/

/-- `set r g ; push k r`: push the glyph `g` onto stack `k`. -/
def pushC (k : Stk) (g : Glyph) (r : Reg) : Cmd := seqs [.set r g, .push k r]

/-- `push k r` when the register `r` holds the glyph `gd`. -/
theorem ev_push_glyph (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    (gd : Glyph) (hg : g r = gd) :
    Ev main (.push k r) ⟨g, X⟩ ⟨g, Function.update X k (gd :: X k)⟩ 1 := by
  have h := ev_push' main k r g X
  rw [hg] at h
  exact h

theorem ev_pushC (main : Cmd) (k : Stk) (gd : Glyph) (r : Reg) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    Ev main (pushC k gd r) ⟨g, X⟩ ⟨Function.update g r gd, Function.update X k (gd :: X k)⟩ 2 := by
  have h1 : Ev main (.set r gd) ⟨g, X⟩ ⟨Function.update g r gd, X⟩ 1 := ev_set' main r gd g X
  have h2 : Ev main (.push k r) ⟨Function.update g r gd, X⟩
      ⟨Function.update g r gd, Function.update X k (gd :: X k)⟩ 1 :=
    ev_push_glyph main k r (Function.update g r gd) X gd (Function.update_self r gd g)
  rw [pushC, seqs_pair]
  exact Ev.seq' h1 h2 (le_rfl)

/-- Push the frame marker of stack `k`. -/
def pushMark (k : Stk) (r : Reg) : Cmd := pushC k (gmk k) r

/-! ## The main loop -/

/-- One iteration of the `shl` block pass: for every `gUnit` glyph of the block region `sP`, pop
it, push two fresh units onto `sT2` (restore + double) and push one zero onto the accumulator
region `sA`. -/
def shlPassBody : Cmd :=
  seqs [.pop sP rX,
        .ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
          (seqs [pushC sT2 gUnit rY, pushC sT2 gUnit rY, pushC sA gZero rY])]

/-- `shl`: the extra unit for a `true` bit of `k`. -/
def shlExtraBody : Cmd := seqs [pushC sT2 gUnit rY, pushC sA gZero rY]

/-- One iteration of the `shr` block pass: pop a `gUnit` glyph of `sP`, push two fresh units onto
`sT2`, and pop one bit of `|a|` from `sM` (recording it in `rD`, stopping the whole computation
via `rE` when the bits of `|a|` run out). -/
def shrPassBody : Cmd :=
  seqs [.pop sP rX,
        .ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
          (seqs [.pop sM rX,
                 .ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
                   (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
                          pushC sT2 gUnit rY, pushC sT2 gUnit rY])])]

/-- `shr`: the extra unit for a `true` bit of `k`. -/
def shrExtraBody : Cmd :=
  seqs [.pop sM rX,
        .ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop])
          (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip, pushC sT2 gUnit rY])]

/-- One iteration of the `shl` outer loop: read the next bit of `k`; if it is `true` push the
extra zero; run the block pass; move the new block back from `sT2` into `sP`. -/
def shlOuterBody : Cmd :=
  seqs [.pop sK rX, .mov rW rX,
        .ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
          (seqs [.set rI gGo,
                 .loop rI gGo shlPassBody,
                 .ite rW (Glyph.bit true) shlExtraBody .skip,
                 drain sT2 sP (gmk sT2) rZ rJ])]

/-- The `shl` main loop. -/
def shlLoop : Cmd := seqs [.set rO gGo, .loop rO gGo shlOuterBody]

/-- One iteration of the `shr` outer loop. -/
def shrOuterBody : Cmd :=
  seqs [.pop sK rX, .mov rW rX,
        .ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
          (seqs [.set rI gGo,
                 .loop rI gGo shrPassBody,
                 .ite rE gStop
                    (seqs [.set rO gStop])
                    (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                           .ite rE gStop (seqs [.set rO gStop])
                             (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])]

/-- The `shr` main loop. -/
def shrLoop : Cmd := seqs [.set rE gNo, .set rD gNo, .set rO gGo, .loop rO gGo shrOuterBody]

/-! ## Increment of the magnitude (for `shrF`) -/

/-- One iteration of the carry-propagating increment of the region of `sM`: a `true` bit is turned
into `false` (the carried `true` is pushed onto `sT`); the first `false` bit is turned into `true`
and the loop stops; if all bits are `true`, a fresh most significant `true` is pushed. -/
def incBody : Cmd :=
  seqs [.pop sM rX,
        .ite rX (gmk sM)
          (seqs [.push sM rX, pushC sM (Glyph.bit true) rY, .set rI gStop])
          (seqs [.ite rX (Glyph.bit true)
                   (pushC sT (Glyph.bit false) rY)
                   (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop])])]

/-- Increase the magnitude region of `sM` by one. -/
def incRgn : Cmd := seqs [.set rI gGo, .loop rI gGo incBody, drain sT sM (gmk sT) rZ rJ]

/-- If `a` is negative (`sSg` holds `neg`) and some dropped bit was `true` (`rD = gAny`), increase
the magnitude region of `sM` by one (the ceiling rounding of `Int.fdiv`). -/
def incIf : Cmd :=
  seqs [.peek sSg rX, .ite rX Glyph.neg (.ite rD gAny incRgn .skip) .skip]

/-! ## Parse, finish, cleanup -/

/-- Split the two input values: sign of `a` in the region of `sSg`, bits of `|a|` (least
significant first) in the region of `sM`, bits of `k` (most significant first) in the region of
`sK`; stack 0 keeps the tail `rest`. -/
def parse : Cmd :=
  seqs [pushMark sSg rY, pushMark sM rY, pushMark sK rY, pushMark sP rY, pushMark sA rY,
        pushMark sT rY, pushMark sT2 rY,
        .pop 0 rX, .push sSg rX,
        drain 0 sT Glyph.iend rZ rJ,
        .pop 0 rX,
        drain sT sM (gmk sT) rZ rJ,
        .pop 0 rX,
        drain 0 sK Glyph.iend rZ rJ,
        .pop 0 rX]

/-- Emit the answer for `shl`: `.int 0` if the magnitude of `a` is zero, else
`sign ++ bits ++ zeros ++ [iend]`. -/
def finishShl : Cmd :=
  seqs [.peek sM rY,
        .ite rY (gmk sM)
          (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY])
          (seqs [pushC 0 Glyph.iend rY,
                 drain sM sT (gmk sM) rZ rJ,
                 drain sT 0 (gmk sT) rZ rJ,
                 drain sA 0 (gmk sA) rZ rJ,
                 .pop sSg rY, .push 0 rY])]

/-- Emit the answer for `shrT`/`shrF`: `.int 0` if the remaining magnitude region is empty, else
`sign ++ bits ++ [iend]`. -/
def finishShr : Cmd :=
  seqs [.peek sM rY,
        .ite rY (gmk sM)
          (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY])
          (seqs [pushC 0 Glyph.iend rY,
                 drain sM sT (gmk sM) rZ rJ,
                 drain sT 0 (gmk sT) rZ rJ,
                 .pop sSg rY, .push 0 rY])]

/-- Restore all scratch stacks. -/
def cleanup : Cmd :=
  seqs [clearAll sSg rZ rJ, clearAll sM rZ rJ, clearAll sK rZ rJ, clearAll sP rZ rJ,
        clearAll sA rZ rJ, clearAll sT rZ rJ, clearAll sT2 rZ rJ]

/-- The `shl` word. -/
def shlProg : Cmd := seqs [parse, shlLoop, finishShl, cleanup]

/-- The `shrT` word. -/
def shrTProg : Cmd := seqs [parse, shrLoop, finishShr, cleanup]

/-- The `shrF` word. -/
def shrFProg : Cmd := seqs [parse, shrLoop, incIf, finishShr, cleanup]

/-! ## Pure list level definitions -/

/-- Value of a most-significant-first bit list, given the value `p` of the preceding bits
(Horner fold: `p ↦ 2p + b`). -/
def natOfMSB (p : ℕ) : List Bool → ℕ
  | [] => p
  | b :: bs => natOfMSB (2 * p + b.toNat) bs

@[simp] theorem natOfMSB_nil (p : ℕ) : natOfMSB p [] = p := rfl

@[simp] theorem natOfMSB_cons (p : ℕ) (b : Bool) (bs : List Bool) :
    natOfMSB p (b :: bs) = natOfMSB (2 * p + b.toNat) bs := rfl

/-- Increment of a natural number, in least-significant-first bit representation. -/
def incList : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: incList xs

@[simp] theorem incList_nil : incList [] = [true] := rfl
@[simp] theorem incList_false (xs : List Bool) : incList (false :: xs) = true :: xs := rfl
@[simp] theorem incList_true (xs : List Bool) : incList (true :: xs) = false :: incList xs := rfl

/-- Cost bound of the `shl` main loop, as a function of the current block length `p` and the list
`R` of (most significant first) bits of `k` that remain to be processed. -/
def shlCost (p : ℕ) : List Bool → ℕ
  | [] => 1
  | b :: bs => (p + 1) + shlCost (2 * p + b.toNat) bs

@[simp] theorem shlCost_nil (p : ℕ) : shlCost p [] = 1 := rfl
@[simp] theorem shlCost_cons (p : ℕ) (b : Bool) (bs : List Bool) :
    shlCost p (b :: bs) = (p + 1) + shlCost (2 * p + b.toNat) bs := rfl

/-- Cost bound of the `shr` main loop: `m` is the number of bits of `|a|` that are still
available. -/
def shrCost (p : ℕ) : List Bool → ℕ → ℕ
  | [], m => m + 1
  | b :: bs, m => if m ≤ p then m + 2 else (p + 1) + shrCost (2 * p + b.toNat) bs (m - p)

@[simp] theorem shrCost_nil (p m : ℕ) : shrCost p [] m = m + 1 := rfl
@[simp] theorem shrCost_cons (p : ℕ) (b : Bool) (bs : List Bool) (m : ℕ) :
    shrCost p (b :: bs) m = if m ≤ p then m + 2 else (p + 1) + shrCost (2 * p + b.toNat) bs (m - p) :=
  rfl

end Shift
end Work.IntLib
