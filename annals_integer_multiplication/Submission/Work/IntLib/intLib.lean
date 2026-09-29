import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.addSubWord
import Submission.Work.IntLib.cmpWord
import Submission.Work.IntLib.mulSWord
import Submission.Work.IntLib.divWord
import Submission.Work.IntLib.sqrtGcdWord
import Submission.Work.IntLib.shiftWord
import Submission.Work.IntLib.sizeWord
import Submission.Work.IntLib.chunkWord
import Submission.Work.IntLib.parseEmitWord

/-! Guidance from the project lead (the requester):

AREA OWNER: IntLib. You prove `HvdH.KernelLib → HvdH.IntLib` (Submission/HvdH/Interfaces.lean, lead-owned).
Read HANDOFF.md and Interfaces.lean (StackLang, `Val.enc`, `WordR`, `BinOp`/`UnOp`, `IntLib`). You may use
the KernelLib hypothesis (seq, conseq, dup, swap, ...) and, once it builds, the raw toolkit in
`Submission/Work/Kernel/` (Raw.lean, Move.lean) — check before re-proving Eval lemmas.
Each field of IntLib is an independent word: delegate them in parallel (one request per group below).

ENCODING: `int z` on stack 0 = [pos|neg] ++ bits of |z| LSB first (no leading zeros; 0 has no bits) ++ [iend];
the top value is `a` in `BinOp` (vs = int a :: int b :: rest). All costs are linear in `isz` except
mulS/tdiv/tmod/fdiv/fmod (product of sizes), sqrt/gcd (square).

SUGGESTED STRUCTURE:
1. `BitStr.lean`: a raw layer on bit strings delimited by markers on scratch stacks: move/copy/reverse a
   bit string, compare two magnitudes, add/subtract magnitudes (with carry in a register), strip leading
   zeros (after a reversing move the MSB is on top — pop zeros there), increment/decrement counters.
   Specs as functions on `List Bool` / `ℕ` via `Nat.bits`/`encodeNat` lemmas (prove `encodeNat` facts:
   length = `Nat.size`, `encodeNat (2n+b) = b :: encodeNat n` for n > 0 etc.).
2. Sign-magnitude wrappers: add/sub/neg/max/lt/eq; shl (insert k zeros after the sign: count down k),
   shrT/shrF (drop min(k, size) low bits; compare k with size FIRST so the cost is O(isz a + isz k), never
   O(k)); size (count bits, amortised O(1) counter increments); clog2; pow2.
3. mulS: schoolbook, loop over the SHORTER operand's bits (cost ≤ K·isz a·isz b needs this).
   tdiv/tmod/fdiv/fmod: long division (shift-subtract), quotient bits × divisor size.
   sqrt: bit-by-bit integer square root; gcd: binary gcd (both O(size²)).
4. chunk (split x into N base-2^b digits, LSB chunk first, zero-padded; cost O(isz x + N(b+1))): keep b as a
   counter copied per chunk; evalPoly (overlap-add Σ h_j 2^{bj} with every h_j < 2^{3b}: the running carry
   stays < 2^{2b+1}, so each step is O(b)).
5. parse (top level): input glyphs `inp a b` (a = bit of x or none, b = bit of y or none), first letter =
   least significant; nothing below the input. Produce `int x` above `int y`. emit: `int z` alone on
   stack 0, stack 1 empty ⇒ stack 1 = `(encodeNat z).map bit` (FIRST bit on top — mind the reversal).
Cost proofs: prove the cost bound with each word (amortised counters: increments cost O(1) amortised,
a counter of value ≤ m has size ≤ size m).
NOT needed: fast multiplication (the main algorithm handles that), anything about ℂ.
Traps: `Int.tdiv`/`Int.fdiv` conventions; `Nat.size 0 = 0`; `isz z = z.natAbs.size + 2`; costs must hold for
ALL inputs satisfying the precondition (negative numbers too).
-/

namespace Work.IntLib

/-- Integer arithmetic words on the value stack.

Assembled from the sibling files of this directory; the words never call `Cmd.self`, so the
`KernelLib` hypothesis is unused. -/
theorem intLib : HvdH.KernelLib → HvdH.IntLib := fun _ =>
  { add := addSubWord.1
    sub := addSubWord.2
    neg := cmpWord.1
    max := cmpWord.2.1
    lt := cmpWord.2.2.1
    eq := cmpWord.2.2.2
    mulS := mulSWord
    tdiv := divWord.1
    tmod := divWord.2.1
    fdiv := divWord.2.2.1
    fmod := divWord.2.2.2
    shl := shiftWord.1
    shrT := shiftWord.2.1
    shrF := shiftWord.2.2
    size := sizeWord.1
    sqrt := sqrtGcdWord.1
    clog2 := sizeWord.2.1
    pow2 := sizeWord.2.2
    gcd := sqrtGcdWord.2
    chunk := chunkWord.1
    evalPoly := chunkWord.2
    parse := parseEmitWord.1
    emit := parseEmitWord.2 }

end Work.IntLib
