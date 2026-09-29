import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Basic
import Submission.Work.Layout.Base

/-!
# IntLib: the `unaryRebuild` gadget — definitions

`unaryRebuild` reads the *reversed* encoding of an integer value off a stack `a`
(`iend :: bs.reverse.map bit ++ [pos]`, i.e. `(Val.enc (int (ofBits bs))).reverse`),
writes the canonical encoding `pos :: bs.map bit ++ [iend]` of the same value on stack `tgt`,
and simultaneously builds the unary counter `Unary (ofBits bs)` on stack `c`.  `tr` is the
scratch stack of the doubling step; every stack is restored.

The work is done by the following program (all registers are 0..6):

* `urLoop` reads the bits MSB-first off `a`; for each bit `b` it
  * pushes the bit glyph onto `tgt` (so `tgt` collects them LSB-first),
  * doubles the unary counter on `c` (`urDouble`) and adds one token when `b = true`;
  it stops when it reads the `pos` that closes the reversed encoding.
* `urDouble` doubles a unary counter on `c` with scratch stack `tr`:
  1. push a sentinel `gEnd` on `tr`,
  2. `urPhase1Loop` moves every token of `c` (and only the tokens, down to the counter's own
     `gEnd` marker) onto `tr`,
  3. `urPhase2Loop` moves the tokens back two at a time,
  4. discard the sentinel.

Cost: `urDouble` costs `9v + 7` for a counter of value `v`; `urLoop` costs
`9·W(p)·(2ⁿ−1) + 18·W(bl) + 16n + 5` where `n = |bl|`, `W(q) = ofBits q.reverse`, `bl` the bits
left to read and `p` the bits already read (the counter then holds `W p`).
-/

set_option autoImplicit false

namespace Work.IntLib
namespace UR

open HvdH

/-! ## Registers -/

/-- Loop register of the main bit loop. -/
def rT : Reg := 0
/-- Register holding the bit currently read. -/
def rB : Reg := 1
/-- Register holding a counter token. -/
def rTok : Reg := 2
/-- Loop register of the two transfer loops. -/
def rD : Reg := 3
/-- Register holding `iend`. -/
def rIend : Reg := 4
/-- Register holding `pos`. -/
def rPos : Reg := 5
/-- Scratch register (discarding a glyph). -/
def rScr : Reg := 6

theorem rTok_ne_rT : rTok ≠ rT := by decide
theorem rB_ne_rT : rB ≠ rT := by decide
theorem rD_ne_rT : rD ≠ rT := by decide
theorem rScr_ne_rT : rScr ≠ rT := by decide
theorem rTok_ne_rD : rTok ≠ rD := by decide
theorem rScr_ne_rD : rScr ≠ rD := by decide
theorem rScr_ne_rTok : rScr ≠ rTok := by decide
theorem rB_ne_rTok : rB ≠ rTok := by decide
theorem rIend_ne_rT : rIend ≠ rT := by decide
theorem rPos_ne_rT : rPos ≠ rT := by decide
theorem rPos_ne_rTok : rPos ≠ rTok := by decide
theorem rIend_ne_rTok : rIend ≠ rTok := by decide
theorem rIend_ne_rD : rIend ≠ rD := by decide
theorem rScr_ne_rB : rScr ≠ rB := by decide
theorem rD_ne_rB : rD ≠ rB := by decide
theorem rIend_ne_rB : rIend ≠ rB := by decide
theorem rPos_ne_rB : rPos ≠ rB := by decide
theorem rIend_ne_rPos : rIend ≠ rPos := by decide
theorem rScr_ne_rPos : rScr ≠ rPos := by decide
theorem rScr_ne_rIend : rScr ≠ rIend := by decide
theorem rD_ne_rPos : rD ≠ rPos := by decide
theorem rD_ne_rIend : rD ≠ rIend := by decide
theorem rD_ne_rScr : rD ≠ rScr := by decide
theorem rB_ne_rD : rB ≠ rD := by decide
theorem rB_ne_rScr : rB ≠ rScr := by decide
theorem rB_ne_rIend : rB ≠ rIend := by decide
theorem rB_ne_rPos : rB ≠ rPos := by decide

/-! ## Glyph distinctness -/

theorem bit_ne_pos (b : Bool) : Glyph.bit b ≠ Glyph.pos := by cases b <;> decide
theorem pos_ne_bit (b : Bool) : Glyph.pos ≠ Glyph.bit b := fun h => bit_ne_pos b h.symm
theorem bit_true_ne_false : (Glyph.bit true : Glyph) ≠ Glyph.bit false := by decide
theorem gEnd_ne_gTok : gEnd ≠ gTok := Work.IntLib.gEnd_ne_gTok
theorem gEnd_ne_pos : gEnd ≠ Glyph.pos := Work.IntLib.gEnd_ne_pos
theorem bit_ne_gTok (b : Bool) : Glyph.bit b ≠ gTok := fun h => Work.IntLib.gTok_ne_bit b h.symm
theorem bit_ne_gEnd (b : Bool) : Glyph.bit b ≠ gEnd := fun h => Work.IntLib.gEnd_ne_bit b h.symm
theorem pos_ne_gTok : Glyph.pos ≠ gTok := fun h => Work.IntLib.gTok_ne_pos h.symm

/-! ## Unary counters -/

/-- `toks n` is `n` copies of the token glyph. -/
def toks (n : ℕ) : List Glyph := List.replicate n gTok

theorem toks_zero : toks 0 = [] := rfl

theorem toks_succ (n : ℕ) : toks (n + 1) = gTok :: toks n := by
  simp only [toks, List.replicate_succ]

theorem toks_head_cons (n : ℕ) : gTok :: toks n = toks (n + 1) := (toks_succ n).symm

theorem toks_add (m n : ℕ) : toks (m + n) = toks m ++ toks n := by
  simp only [toks, List.replicate_add]

theorem toks_append_Unary (v j : ℕ) (Tr : List Glyph) :
    toks v ++ Unary j Tr = Unary (v + j) Tr := by
  simp only [toks, Unary, List.replicate_add, List.append_assoc]

theorem Unary_headD (v : ℕ) (Gc : List Glyph) (d : Glyph) :
    (Unary v Gc).headD d = if v = 0 then gEnd else gTok := by
  cases v with
  | zero => simp [Unary]
  | succ v => simp [Unary_succ]

theorem Unary_headD_ne {v : ℕ} (Gc : List Glyph) (d : Glyph) (hv : v ≠ 0) :
    (Unary v Gc).headD d = gTok := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
  simp [Unary_succ]

theorem Unary_headD_zero (Gc : List Glyph) (d : Glyph) : (Unary 0 Gc).headD d = gEnd := by
  simp [Unary]

theorem Unary_ne_gTok_zero (Gc : List Glyph) (d : Glyph) :
    (Unary 0 Gc).headD d ≠ gTok := by
  rw [Unary_headD_zero]; exact gEnd_ne_gTok

theorem Unary_tail_succ (v : ℕ) (Gc : List Glyph) : (Unary (v + 1) Gc).tail = Unary v Gc := by
  simp [Unary_succ]

theorem Unary_head_eq (v : ℕ) (Gc : List Glyph) (hv : v ≠ 0) :
    Unary v Gc = gTok :: Unary (v - 1) Gc := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
  simp [Unary_succ]

/-! ## The value of the bits processed so far -/

/-- `urW p` is the integer represented by the bits `p` (in the order in which they are read,
i.e. most significant first). -/
def urW (p : List Bool) : ℕ := ofBits p.reverse

theorem urW_nil : urW [] = 0 := rfl

theorem urW_reverse (bs : List Bool) : urW bs.reverse = ofBits bs := by simp [urW]

theorem urW_snoc (p : List Bool) (b : Bool) : urW (p ++ [b]) = b.toNat + 2 * urW p := by
  have h : (p ++ [b]).reverse = b :: p.reverse := by simp
  simp only [urW, h, ofBits_cons]

theorem urW_cons (b : Bool) (bl : List Bool) :
    urW (b :: bl) = 2 ^ bl.length * b.toNat + urW bl := by
  have h : (b :: bl).reverse = bl.reverse ++ [b] := by simp
  have hb : ofBits [b] = b.toNat := by cases b <;> rfl
  simp only [urW, h, ofBits_append, List.length_reverse, hb]
  ring

theorem urW_append (p q : List Bool) : urW (p ++ q) = urW q + 2 ^ q.length * urW p := by
  have h : (p ++ q).reverse = q.reverse ++ p.reverse := by simp
  simp only [urW, h, ofBits_append, List.length_reverse]

/-- The cost recurrence of `urLoop`: one more bit `b` (value `b.toNat`), `2^m` the value of the
remaining bits, `A` the counter so far, `B` the value of what is left. -/
theorem ur_bound_step (A b B m : ℕ) :
    9 * A + 16 + (9 * (b + 2 * A) * (2 ^ m - 1) + 18 * B + 16 * m + 5) ≤
      9 * A * (2 ^ (m + 1) - 1) + 18 * (2 ^ m * b + B) + 16 * (m + 1) + 5 := by
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  set u : ℕ := 2 ^ m - 1 with hu
  have h2m : 2 ^ m = u + 1 := by omega
  have h2m1 : 2 ^ (m + 1) - 1 = 2 * u + 1 := by
    have h : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    omega
  rw [h2m1, h2m]
  nlinarith

/-! ## Programs -/

/-- One transfer step of `urPhase1Loop`. -/
def urPhase1Body (c tr : Stk) : Cmd :=
  .seq (.pop c rD) (.seq (.push tr rD) (.peek c rD))

/-- Move every token of the counter on `c` (above its `gEnd` marker) onto `tr`. -/
def urPhase1Loop (c tr : Stk) : Cmd := .loop rD gTok (urPhase1Body c tr)

/-- One doubling step of `urPhase2Loop`. -/
def urPhase2Body (c tr : Stk) : Cmd :=
  .seq (.pop tr rD) (.seq (.push c rTok) (.seq (.push c rTok) (.peek tr rD)))

/-- Move the tokens back from `tr` to `c`, two per token. -/
def urPhase2Loop (c tr : Stk) : Cmd := .loop rD gTok (urPhase2Body c tr)

/-- Double the unary counter on `c`, using `tr` as scratch. -/
def urDouble (c tr : Stk) : Cmd :=
  .seq (.set rD gEnd)
    (.seq (.push tr rD)
      (.seq (.peek c rD)
        (.seq (urPhase1Loop c tr)
          (.seq (.peek tr rD)
            (.seq (urPhase2Loop c tr) (.pop tr rScr))))))

/-- One iteration of the main loop: read one bit (or the closing `pos`). -/
def urLoopBody (a tgt c tr : Stk) : Cmd :=
  .seq (.pop a rT)
    (.ite rT Glyph.pos (.set rT gEnd)
      (.seq (.mov rB rT)
        (.seq (.set rT gTok)
          (.seq (.push tgt rB)
            (.seq (urDouble c tr)
              (.ite rB (Glyph.bit true) (.push c rTok) .skip))))))

/-- The main loop: read the bits off `a` until the closing `pos`. -/
def urLoop (a tgt c tr : Stk) : Cmd := .loop rT gTok (urLoopBody a tgt c tr)

/-- The whole `unaryRebuild` program. -/
def urProg (a tgt c tr : Stk) : Cmd :=
  .seq (.set rIend Glyph.iend)
    (.seq (.push tgt rIend)
      (.seq (.set rTok gTok)
        (.seq (.set rPos Glyph.pos)
          (.seq (.set rScr gEnd)
            (.seq (.push c rScr)
              (.seq (.pop a rScr)
                (.seq (.set rT gTok)
                  (.seq (urLoop a tgt c tr)
                    (.seq (.set rPos Glyph.pos)
                      (.seq (.push tgt rPos) .skip))))))))))

end UR
end Work.IntLib
