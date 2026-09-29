import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.mulSEvKit
import Submission.Work.IntLib.mulSEv
import Submission.Work.IntLib.mulSArith
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.stripFalses_map_bit
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.encodeNatBridge

/-!
# A schoolbook natural-multiplication word: definitions

`Work.Resample.MulNW` contains a StackLang word `mulProg` that replaces the two natural-number
values on top of the value stack by their product, at schoolbook cost
`K * (size a + 1) * (size b + 1)`.

Stack layout (all scratch stacks carry a frame marker at the bottom of the region the program
uses, so arbitrary pre-existing content below is preserved, and is restored exactly at the end):

* stack 0 : the value stack, holding `int a :: int b :: rest` to begin with;
* `sA` (1): the bits of `a`, least significant bit first, above marker `mkA`;
* `sB` (2): the bits of `b`, least significant bit first, above marker `mkB`;
* `sR` (3): the running remainder `ρ` (`size a` bits, least significant first), above `mkR`;
* `sC` (4): the accumulated output bits, most significant first, above `mkC`;
* `sS` (5): the two sign glyphs, above marker `mkS`;
* `sT` (6): scratch (addition buffer / bit transport), above marker `mkT`;
* `sW` (7): scratch (saved copy of the bits of `a`), above marker `mkW`;
* `sU` (8): scratch (bit assembly), above marker `mkU`.

The primitive `consume` is `Work.IntLib.consume` (whose loop sentinel is `Glyph.mk 0`); its general
specification `Work.IntLib.consume_eval` is used throughout.
-/

set_option autoImplicit false

namespace Work.Resample
namespace MulNW

open HvdH

/-! ## Stacks, markers, registers -/

abbrev sA : Stk := 1
abbrev sB : Stk := 2
abbrev sR : Stk := 3
abbrev sC : Stk := 4
abbrev sS : Stk := 5
abbrev sT : Stk := 6
abbrev sW : Stk := 7
abbrev sU : Stk := 8

abbrev mkA : Glyph := .mk 1
abbrev mkB : Glyph := .mk 2
abbrev mkR : Glyph := .mk 3
abbrev mkC : Glyph := .mk 4
abbrev mkS : Glyph := .mk 5
abbrev mkT : Glyph := .mk 6
abbrev mkW : Glyph := .mk 7
abbrev mkU : Glyph := .mk 8
/-- loop sentinel of `stripProg` (never `eos`, never a marker, never a `Val.enc` glyph) -/
abbrev mkStop : Glyph := .mk 9

abbrev rL : Reg := 0
abbrev rBit : Reg := 1
abbrev rA : Reg := 2
abbrev rRho : Reg := 3
abbrev rCy : Reg := 4
abbrev rS : Reg := 5
abbrev rZ : Reg := 6
abbrev rIe : Reg := 7
abbrev rSign : Reg := 8
abbrev rTmp : Reg := 9
abbrev rOut : Reg := 10

/-! ## Tools from the shared toolkit -/

/-- `consume`: pop glyphs from `k` up to the frame marker `T`, feeding each one to `handler`;
the loop register is set to `Glyph.mk 0` on exit.  (Identical to `Work.IntLib.consume`.) -/
abbrev consume (k : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  Work.IntLib.consume k T r handler

/-- Abbreviation for the raw consume-loop of the shared toolkit. -/
abbrev consumeLoop : Stk → Glyph → Reg → Cmd → Cmd := Work.IntLib.consumeLoop

/-- Abbreviation for the schoolbook `stepR` of the arithmetic layer. -/
abbrev stepR : List Bool → List Bool → Bool → Bool × List Bool := Work.IntLib.MulS.stepR

/-- Abbreviation for the schoolbook multiplier loop function. -/
abbrev run : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool :=
  Work.IntLib.MulS.run

/-- Abbreviation for the ripple-carry bit addition. -/
abbrev addBits : List Bool → List Bool → Bool → List Bool × Bool := Work.IntLib.MulS.addBits

/-- Abbreviation for the full-adder sum bit. -/
abbrev faSum : Bool → Bool → Bool → Bool := Work.IntLib.MulS.faSum

/-- Abbreviation for the full-adder carry bit. -/
abbrev faCarry : Bool → Bool → Bool → Bool := Work.IntLib.MulS.faCarry

/-- Abbreviation for the padding of the multiplicand bit list. -/
abbrev padFalse : List Bool → Bool → List Bool := Work.IntLib.MulS.padFalse

/-- `bitsG l` is the glyph image of the bit list `l` (least significant bit first). -/
abbrev bitsG (l : List Bool) : List Glyph := l.map Glyph.bit

/-- The bits of `n`, least significant bit first, as glyphs. -/
abbrev natBits (n : ℕ) : List Glyph := bitsG n.bits

/-- The `m` zero bits of the (padded) remainder `ρ`. -/
abbrev zeros (m : ℕ) : List Bool := List.replicate m false

/-! ## The program -/

/-- The `(glyph, stack)` pairs whose markers `openProg` pushes. -/
def marks : List (Glyph × Stk) :=
  [(mkA, sA), (mkB, sB), (mkR, sR), (mkC, sC), (mkS, sS), (mkT, sT), (mkW, sW), (mkU, sU)]

/-- `markPush r l`: for every pair `(g, k)` of `l`, set register `r` to `g` and push it on `k`. -/
def markPush (r : Reg) : List (Glyph × Stk) → Cmd
  | [] => .skip
  | p :: l => .seq (.seq (.set r p.1) (.push p.2 r)) (markPush r l)

/-- push the eight frame markers, and set up the two constant registers -/
def openProg : Cmd :=
  .seq (markPush rTmp marks) (.seq (.set rZ (Glyph.bit false)) (.set rIe Glyph.iend))

/-- peel the two input values off stack 0: signs to `sS`, bits of `a` to `sA`, bits of `b` to `sB` -/
def peelProg : Cmd := Work.IntLib.MulS.seqs [
  .pop 0 rSign, .push sS rSign,
  consume 0 Glyph.iend rL (.push sW rL),
  .pop 0 rTmp,
  consume sW mkW rL (.push sA rL),
  .pop 0 rSign, .push sS rSign,
  consume 0 Glyph.iend rL (.push sT rL),
  .pop 0 rTmp,
  consume sT mkT rL (.push sB rL) ]

/-- initialise the remainder `ρ` to `size a` zero bits, keeping the bits of `a` on `sA` -/
def initRProg : Cmd := Work.IntLib.MulS.seqs [
  .set rZ (Glyph.bit false),
  consume sA mkA rL (Work.IntLib.MulS.seqs [.push sW rL, .push sR rZ]),
  consume sW mkW rL (.push sA rL) ]

/-- one bit position of the inner addition: `ρ += (β ? α : 0)`, output bit to `sT` -/
def addABody : Cmd := Work.IntLib.MulS.seqs [
  .push sW rL,
  .pop sR rRho,
  .mov rA rL,
  .ite rBit (Glyph.bit true) .skip (.set rA (Glyph.bit false)),
  Work.IntLib.MulS.fullAdd,
  .push sT rS ]

/-- add `(β ? |a| : 0)` into `ρ`, output the low bit of the sum to `sC`, halve `ρ`; restore `sA` -/
def addAProg : Cmd := Work.IntLib.MulS.seqs [
  .set rCy (Glyph.bit false),
  consume sA mkA rL addABody,
  .push sT rCy,
  consume sT mkT rL (.push sR rL),
  consume sW mkW rL (.push sA rL),
  .pop sR rOut, .push sC rOut ]

/-- body of the multiplier loop: `rL` holds the next bit `β` of `|b|` -/
def mainBody : Cmd := .seq (.mov rBit rL) addAProg

/-- the serial multiplier loop over the bits of `b` -/
def mainLoopProg : Cmd := consume sB mkB rL mainBody

/-- drop the (high) zero bits on top of `sC` -/
def stripProg : Cmd := Work.IntLib.stripZeros sC mkC rTmp

/-- compute the sign of the product into `rSign` from the two stored sign glyphs -/
def sgnProg : Cmd := Work.IntLib.MulS.seqs [
  .pop sS rBit, .pop sS rA, .pop sS rTmp,
  .ite rA Glyph.neg (.ite rBit Glyph.neg (.set rSign Glyph.pos) (.set rSign Glyph.neg))
    (.ite rBit Glyph.neg (.set rSign Glyph.neg) (.set rSign Glyph.pos)) ]

/-- assemble the product value on stack 0 -/
def finalizeProg : Cmd := Work.IntLib.MulS.seqs [
  consume sR mkR rL (.push sT rL),
  consume sT mkT rL (.push sU rL),
  consume sC mkC rL (.push sU rL),
  consume sU mkU rL (.push sC rL),
  stripProg,
  .set rIe Glyph.iend,
  .push 0 rIe,
  sgnProg,
  .peek sC rTmp,
  .ite rTmp (Glyph.bit false) (.set rSign Glyph.pos) .skip,
  consume sC mkC rL (.push 0 rL),
  .set rSign Glyph.pos,
  .push 0 rSign ]

/-- pop all remaining frame markers, restoring the scratch stacks -/
def closeProg : Cmd := Work.IntLib.MulS.seqs [
  consume sA mkA rL .skip,
  .pop sA rTmp, .pop sB rTmp, .pop sR rTmp, .pop sC rTmp,
  .pop sT rTmp, .pop sW rTmp, .pop sU rTmp ]

/-- the whole schoolbook multiplication word -/
def mulProg : Cmd :=
  .seq openProg (.seq peelProg (.seq initRProg (.seq mainLoopProg
    (.seq finalizeProg closeProg))))


/-! ## The specification of the inner addition phase (`addAProg`) as a named `Prop`

`AddASpec main` is the statement of the phase lemma for `addAProg`: it adds `(β ? α : 0)` to the
remainder `ρ` (both of length `n`), emits the low bit of the sum on `sC`, and leaves the halved
remainder on `sR`, keeping the framing content of every stack.  It is factored out as a definition
so that the multiplier-loop phase can be stated and proved against it (and instantiated with the
proof of `Work.Resample.MulNW.addA_ev`).
-/
def AddASpec (main : Cmd) : Prop :=
  ∀ (α ρ : List Bool) (β : Bool) (bkA bkR bkW bkT : List Glyph) (s : State),
    ρ.length = α.length →
    s.stk sA = bitsG α ++ mkA :: bkA →
    s.stk sR = bitsG ρ ++ mkR :: bkR →
    s.stk sW = mkW :: bkW →
    s.stk sT = mkT :: bkT →
    s.reg rBit = Glyph.bit β →
    ∃ s' n, Eval main addAProg s s' n ∧ n ≤ 30 * (α.length + 2) ∧
      s'.stk sA = bitsG α ++ mkA :: bkA ∧
      s'.stk sR = bitsG ((Work.IntLib.MulS.stepR α ρ β).2) ++ mkR :: bkR ∧
      s'.stk sC = Glyph.bit ((Work.IntLib.MulS.stepR α ρ β).1) :: s.stk sC ∧
      s'.stk sW = mkW :: bkW ∧ s'.stk sT = mkT :: bkT ∧
      (∀ j, j ∉ ({sA, sC, sR, sT, sW} : Finset Stk) → s'.stk j = s.stk j)


/-! ## The specifications of the six phases, as named `Prop`s

Each phase lemma's statement is packaged as a `def …Spec : Prop` so that the pieces can be
requested/delegated with one-line statements, and so that a phase can be assumed as a hypothesis
while the phase below it is still under construction.
-/

/-- `openProg`: push the eight frame markers and set up the two constant registers. -/
def OpenSpec (main : Cmd) : Prop :=
  ∀ (s : State), ∃ (s' : State) (n : ℕ), Eval main openProg s s' n ∧ n ≤ 20 ∧
      s'.stk 0 = s.stk 0 ∧
      s'.stk sA = mkA :: s.stk sA ∧ s'.stk sB = mkB :: s.stk sB ∧
      s'.stk sR = mkR :: s.stk sR ∧ s'.stk sC = mkC :: s.stk sC ∧
      s'.stk sS = mkS :: s.stk sS ∧ s'.stk sT = mkT :: s.stk sT ∧
      s'.stk sW = mkW :: s.stk sW ∧ s'.stk sU = mkU :: s.stk sU ∧
      (∀ j, j ∉ ({0, sA, sB, sR, sC, sS, sT, sW, sU} : Finset Stk) → s'.stk j = s.stk j)

/-- `peelProg`: peel the two input values off stack 0 (signs to `sS`, bits of `a` to `sA`, bits of
`b` to `sB`). -/
def PeelSpec (main : Cmd) (a b : ℕ) (rest : List Val) (R : List Glyph) : Prop :=
  ∀ (bkT bkW : List Glyph) (s : State),
    s.stk 0 = encs (.int a :: .int b :: rest) ++ R →
    s.stk sW = mkW :: bkW → s.stk sT = mkT :: bkT →
    ∃ (s' : State) (n : ℕ), Eval main peelProg s s' n ∧ n ≤ 40 * (a.size + b.size + 2) ∧
      s'.stk 0 = encs rest ++ R ∧
      s'.stk sA = natBits a ++ s.stk sA ∧
      s'.stk sB = natBits b ++ s.stk sB ∧
      s'.stk sS = Glyph.pos :: Glyph.pos :: s.stk sS ∧
      s'.stk sW = s.stk sW ∧ s'.stk sT = s.stk sT ∧
      (∀ j, j ∉ ({0, sA, sB, sS, sT, sW} : Finset Stk) → s'.stk j = s.stk j)

/-- `initRProg`: initialise the remainder `ρ` to `size a` zero bits, keeping the bits of `a` on
`sA`. -/
def InitRSpec (main : Cmd) (a : ℕ) : Prop :=
  ∀ (bkA bkW bkR : List Glyph) (s : State),
    s.stk sA = natBits a ++ mkA :: bkA → s.stk sW = mkW :: bkW → s.stk sR = bkR →
    ∃ (s' : State) (n : ℕ), Eval main initRProg s s' n ∧ n ≤ 30 * (a.size + 1) ∧
      s'.stk sA = natBits a ++ mkA :: bkA ∧ s'.stk sW = mkW :: bkW ∧
      s'.stk sR = bitsG (zeros a.size) ++ bkR ∧
      (∀ j, j ∉ ({sA, sR, sW} : Finset Stk) → s'.stk j = s.stk j)

/-- `closeProg`: pop the remaining frame markers, restoring the scratch stacks. -/
def CloseSpec (main : Cmd) (a : ℕ) : Prop :=
  ∀ (bkA bkB bkR bkC bkT bkW bkU : List Glyph) (s : State),
    s.stk sA = natBits a ++ mkA :: bkA →
    s.stk sB = mkB :: bkB →
    s.stk sR = mkR :: bkR → s.stk sC = mkC :: bkC →
    s.stk sT = mkT :: bkT → s.stk sW = mkW :: bkW → s.stk sU = mkU :: bkU →
    ∃ (s' : State) (n : ℕ), Eval main closeProg s s' n ∧ n ≤ 10 * (a.size + 2) ∧
      s'.stk sA = bkA ∧ s'.stk sB = bkB ∧ s'.stk sR = bkR ∧ s'.stk sC = bkC ∧
      s'.stk sT = bkT ∧ s'.stk sW = bkW ∧ s'.stk sU = bkU ∧
      (∀ j, j ∉ ({sA, sB, sR, sC, sT, sW, sU} : Finset Stk) → s'.stk j = s.stk j)

/-- `mainLoopProg`: the serial multiplier loop over the bits of `b`. -/
def MainLoopSpec (main : Cmd) (a b : ℕ) : Prop :=
  ∀ (bkA bkB bkR bkC bkW bkT : List Glyph) (s : State),
    s.stk sA = natBits a ++ mkA :: bkA →
    s.stk sB = natBits b ++ mkB :: bkB →
    s.stk sR = bitsG (zeros a.size) ++ mkR :: bkR →
    s.stk sC = mkC :: bkC →
    s.stk sW = mkW :: bkW → s.stk sT = mkT :: bkT →
    ∃ (s' : State) (n : ℕ), Eval main mainLoopProg s s' n ∧
      n ≤ 110 * (a.size + 1) * (b.size + 1) ∧
      s'.stk sB = mkB :: bkB ∧
      s'.stk sR = bitsG ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2) ++ mkR :: bkR ∧
      s'.stk sC = bitsG ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1) ++ mkC :: bkC ∧
      s'.stk sA = natBits a ++ mkA :: bkA ∧
      s'.stk sW = mkW :: bkW ∧ s'.stk sT = mkT :: bkT ∧
      (∀ j, j ∉ ({sA, sB, sC, sR, sT, sW} : Finset Stk) → s'.stk j = s.stk j)

/-- `finalizeProg`: assemble `int (a * b)` on stack 0. -/
def FinalizeSpec (main : Cmd) (a b : ℕ) (rest : List Val) (R : List Glyph) : Prop :=
  ∀ (ha : 1 ≤ a) (hb : 1 ≤ b) (bkS bkR bkC bkT bkW bkU : List Glyph) (s : State),
    s.stk 0 = encs rest ++ R →
    s.stk sS = Glyph.pos :: Glyph.pos :: mkS :: bkS →
    s.stk sR = bitsG ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2) ++ mkR :: bkR →
    s.stk sC = bitsG ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1) ++ mkC :: bkC →
    s.stk sW = mkW :: bkW → s.stk sT = mkT :: bkT → s.stk sU = mkU :: bkU →
    ∃ (s' : State) (n : ℕ), Eval main finalizeProg s s' n ∧ n ≤ 60 * (a.size + b.size + 4) ∧
      s'.stk 0 = encs (.int (a * b) :: rest) ++ R ∧
      s'.stk sS = bkS ∧
      s'.stk sR = mkR :: bkR ∧ s'.stk sC = mkC :: bkC ∧
      s'.stk sT = mkT :: bkT ∧ s'.stk sW = mkW :: bkW ∧ s'.stk sU = mkU :: bkU ∧
      (∀ j, j ∉ ({0, sR, sC, sS, sT, sW, sU} : Finset Stk) → s'.stk j = s.stk j)

/-! ## Unfolding lemmas for the arithmetic layer -/

theorem run_nil (α acc ρ : List Bool) : run α [] acc ρ = (acc, ρ) := rfl

theorem run_cons (α : List Bool) (b : Bool) (bs acc ρ : List Bool) :
    run α (b :: bs) acc ρ =
      (let s := stepR α ρ b; run α bs (s.1 :: acc) s.2) := rfl

/-! ## Elementary facts about the layout -/

theorem bitsG_append (l₁ l₂ : List Bool) : bitsG (l₁ ++ l₂) = bitsG l₁ ++ bitsG l₂ :=
  List.map_append

theorem bitsG_nil : bitsG ([] : List Bool) = [] := rfl

theorem bitsG_cons (b : Bool) (l : List Bool) : bitsG (b :: l) = Glyph.bit b :: bitsG l := rfl

theorem bitsG_reverse (l : List Bool) : bitsG l.reverse = (bitsG l).reverse :=
  List.map_reverse

/-- From `g :: gs = bitsG l`, extract the head bit and the tail list. -/
theorem exists_of_bitglyph_head {g : Glyph} {gs : List Glyph} {l : List Bool}
    (h : g :: gs = bitsG l) : ∃ (b : Bool) (l' : List Bool), g = Glyph.bit b ∧ gs = bitsG l' := by
  cases l with
  | nil => simp [bitsG] at h
  | cons b l' =>
    refine ⟨b, l', ?_, ?_⟩
    · simpa [bitsG] using congrArg (fun (x : List Glyph) => x.headD Glyph.eos) h
    · simpa [bitsG] using (List.cons.inj h).2

theorem bit_ne_mk (b : Bool) (i : Fin 16) : Glyph.bit b ≠ Glyph.mk i := by
  intro h; cases h

theorem bit_ne_eos (b : Bool) : Glyph.bit b ≠ Glyph.eos := by
  intro h; cases h

theorem lit_ne_mk (i j : Fin 16) (h : i ≠ j) : Glyph.mk i ≠ Glyph.mk j := by
  intro hh; exact h (Glyph.mk.inj hh)

theorem bitsG_ne_mkA (l : List Bool) : ∀ g ∈ bitsG l, ∀ i : Fin 16, g ≠ Glyph.mk i := by
  intro g hg i
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
  exact fun h => by cases h

theorem bitsG_ne_iend (l : List Bool) : ∀ g ∈ bitsG l, g ≠ Glyph.iend := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
  exact fun h => by cases h

theorem bitsG_ne_eos (l : List Bool) : ∀ g ∈ bitsG l, g ≠ Glyph.eos := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
  exact fun h => by cases h

theorem not_bit_false_ne {g : Glyph} (h : g ≠ Glyph.bit false) : (g = Glyph.bit false) = False :=
  eq_false h

end MulNW
end Work.Resample
