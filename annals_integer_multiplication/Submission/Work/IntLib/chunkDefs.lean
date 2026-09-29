import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.Layout.Base

/-!
# IntLib: shared definitions for the `chunk` / `evalPoly` words

The `chunk` word of `HvdH.IntLib` splits `x < 2^(b*N)` into its `N` base-`2^b` digits by reading the
*canonical bit encoding* of `x` off the value stack; the `evalPoly` word evaluates
`hs ↦ Σ_j hs[j]·2^(b j)` by overlap-add.  Both programs use

* **marker glyphs** `Glyph.mk _` that never occur in a value encoding, to delimit scratch data on
  the shared stacks (`gBot` at the bottom of every scratch region, `gTok`/`gEnd` for unary
  counters), so that every touched stack can be restored to whatever it held before;
* **unary counters** (`Unary n rest = gTok^n ++ gEnd :: rest`) as loop counters, because the machine
  has no arithmetic on registers;
* **bit streams**: a value `int x` is stored on a stack as `pos :: x.bits.map bit ++ [iend]`
  (least significant bit on top), so reading it destructively hands the bits low-to-high.

This file fixes those conventions and states the (program-level) gadget lemmas proved in the
sibling files of `Submission/Work/IntLib/`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Marker glyphs -/

/-- Bottom marker of stack `k`: pushed first on every scratch stack, so that everything above it
can be deleted at the end (via `Work.IntLib.Shift.clearAll k`) and whatever the caller had on that
stack is restored.  The data of the `chunk`/`evalPoly` words (bits, `gTok`, `gEnd`) never contains
`gmk k` for the stack `k` it is stored on, so the marker test is unambiguous. -/
def gmk (k : Stk) : Glyph := .mk k

/-- Bottom marker used on all scratch stacks in the informal descriptions of this directory. -/
def gBot : Glyph := .mk 15

/-- One unit of a unary counter. -/
def gTok : Glyph := .mk 14

/-- Sentinel sitting below the units of a unary counter. -/
def gEnd : Glyph := .mk 13

theorem gBot_ne_gTok : gBot ≠ gTok := by decide
theorem gBot_ne_gEnd : gBot ≠ gEnd := by decide
theorem gTok_ne_gEnd : gTok ≠ gEnd := by decide
theorem gTok_ne_gBot : gTok ≠ gBot := fun h => gBot_ne_gTok h.symm
theorem gEnd_ne_gBot : gEnd ≠ gBot := fun h => gBot_ne_gEnd h.symm
theorem gEnd_ne_gTok : gEnd ≠ gTok := fun h => gTok_ne_gEnd h.symm

theorem gBot_ne_bit (b : Bool) : gBot ≠ Glyph.bit b := fun h => by cases h
theorem gBot_ne_pos : gBot ≠ Glyph.pos := fun h => by cases h
theorem gBot_ne_neg : gBot ≠ Glyph.neg := fun h => by cases h
theorem gBot_ne_iend : gBot ≠ Glyph.iend := fun h => by cases h
theorem gBot_ne_nil : gBot ≠ Glyph.nil := fun h => by cases h
theorem gBot_ne_cons : gBot ≠ Glyph.cons := fun h => by cases h
theorem gBot_ne_eos : gBot ≠ Glyph.eos := fun h => by cases h

theorem gTok_ne_bit (b : Bool) : gTok ≠ Glyph.bit b := fun h => by cases h
theorem gEnd_ne_bit (b : Bool) : gEnd ≠ Glyph.bit b := fun h => by cases h

theorem gTok_ne_pos : gTok ≠ Glyph.pos := fun h => by cases h
theorem gTok_ne_neg : gTok ≠ Glyph.neg := fun h => by cases h
theorem gTok_ne_iend : gTok ≠ Glyph.iend := fun h => by cases h
theorem gTok_ne_nil : gTok ≠ Glyph.nil := fun h => by cases h
theorem gTok_ne_cons : gTok ≠ Glyph.cons := fun h => by cases h
theorem gTok_ne_eos : gTok ≠ Glyph.eos := fun h => by cases h

theorem gEnd_ne_pos : gEnd ≠ Glyph.pos := fun h => by cases h
theorem gEnd_ne_neg : gEnd ≠ Glyph.neg := fun h => by cases h
theorem gEnd_ne_iend : gEnd ≠ Glyph.iend := fun h => by cases h
theorem gEnd_ne_nil : gEnd ≠ Glyph.nil := fun h => by cases h
theorem gEnd_ne_cons : gEnd ≠ Glyph.cons := fun h => by cases h
theorem gEnd_ne_eos : gEnd ≠ Glyph.eos := fun h => by cases h

/-- A glyph that is not one of the three structural glyphs `cons`, `nil`, `iend`. -/
def NotStruct (h : Glyph) : Prop := h ≠ Glyph.cons ∧ h ≠ Glyph.nil ∧ h ≠ Glyph.iend

theorem notStruct_bit (b : Bool) : NotStruct (Glyph.bit b) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
theorem notStruct_pos : NotStruct Glyph.pos := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
theorem notStruct_neg : NotStruct Glyph.neg := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

theorem not_mem_map_bit (x : Glyph) (hx : ∀ b, x ≠ Glyph.bit b) (bs : List Bool) :
    x ∉ bs.map Glyph.bit := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact hx b hb.symm

theorem gBot_not_mem_enc (v : Val) : gBot ∉ v.enc := by
  induction v with
  | int z =>
      intro hmem
      simp only [Val.enc] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · by_cases hz : z < 0
        · rw [if_pos hz] at h; exact gBot_ne_neg h
        · rw [if_neg hz] at h; exact gBot_ne_pos h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_map_bit _ (fun b => gBot_ne_bit b) _ h
        · exact gBot_ne_iend (List.mem_singleton.mp h)
  | nil => intro h; simp only [Val.enc, List.mem_singleton] at h; exact gBot_ne_nil h
  | cons a b iha ihb =>
      intro hmem
      simp only [Val.enc, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact gBot_ne_cons h
      · exact (List.mem_append.mp h).elim iha ihb

theorem gTok_not_mem_enc (v : Val) : gTok ∉ v.enc := by
  induction v with
  | int z =>
      intro hmem
      simp only [Val.enc] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · by_cases hz : z < 0
        · rw [if_pos hz] at h; exact gTok_ne_neg h
        · rw [if_neg hz] at h; exact gTok_ne_pos h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_map_bit _ (fun b => gTok_ne_bit b) _ h
        · exact gTok_ne_iend (List.mem_singleton.mp h)
  | nil => intro h; simp only [Val.enc, List.mem_singleton] at h; exact gTok_ne_nil h
  | cons a b iha ihb =>
      intro hmem
      simp only [Val.enc, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact gTok_ne_cons h
      · exact (List.mem_append.mp h).elim iha ihb

theorem gEnd_not_mem_enc (v : Val) : gEnd ∉ v.enc := by
  induction v with
  | int z =>
      intro hmem
      simp only [Val.enc] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · by_cases hz : z < 0
        · rw [if_pos hz] at h; exact gEnd_ne_neg h
        · rw [if_neg hz] at h; exact gEnd_ne_pos h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_map_bit _ (fun b => gEnd_ne_bit b) _ h
        · exact gEnd_ne_iend (List.mem_singleton.mp h)
  | nil => intro h; simp only [Val.enc, List.mem_singleton] at h; exact gEnd_ne_nil h
  | cons a b iha ihb =>
      intro hmem
      simp only [Val.enc, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact gEnd_ne_cons h
      · exact (List.mem_append.mp h).elim iha ihb

theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons x y => simp [vsz, Val.enc]

/-! ## Unary counters -/

/-- The content of a unary counter with `n` units, above the stack's tail `rest`. -/
def Unary (n : ℕ) (rest : List Glyph) : List Glyph := List.replicate n gTok ++ gEnd :: rest

@[simp] theorem Unary_zero (rest : List Glyph) : Unary 0 rest = gEnd :: rest := rfl

theorem Unary_succ (n : ℕ) (rest : List Glyph) : Unary (n + 1) rest = gTok :: Unary n rest := by
  simp [Unary, List.replicate_succ]

theorem Unary_eq_append (n : ℕ) (rest : List Glyph) :
    Unary n rest = List.replicate n gTok ++ (gEnd :: rest) := rfl

theorem Unary_head {n : ℕ} {rest : List Glyph} (hn : 1 ≤ n) : (Unary n rest).headD gBot = gTok := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 1 + m = m + 1 from Nat.add_comm 1 m, Unary_succ]
  rfl

theorem Unary_head_zero (rest : List Glyph) : (Unary 0 rest).headD gBot = gEnd := by
  simp

/-- Value of a list of bits given most significant first. -/
def bitsVal (bs : List Bool) : ℕ := ofBits bs.reverse

theorem bitsVal_nil : bitsVal [] = 0 := rfl

theorem bitsVal_eq_ofBits_reverse (bs : List Bool) : bitsVal bs = ofBits bs.reverse := rfl

theorem bitsVal_cons (b : Bool) (bs : List Bool) :
    bitsVal (b :: bs) = 2 ^ bs.length * b.toNat + bitsVal bs := by
  simp only [bitsVal_eq_ofBits_reverse, List.reverse_cons]
  rw [ofBits_append]
  simp [ofBits, Nat.add_comm]

/-! ## Digits of a bit stream -/

/-- The `N` base-`2^b` digits read off the bit stream `bs` (least significant bit first). -/
def chunkDigits (bs : List Bool) (b N : ℕ) : List ℕ :=
  (List.range N).map (fun j => ofBits ((bs.drop (b * j)).take b))

/-! ## The glyph order pushed by the `chunk` loop

The `chunk` word builds the encoding of `intList (chunks x b N)` on a scratch stack by pushing, for
each group of `b` bits, `cons`, `pos`, the bits of the digit (low to high, with the trailing zero
bits deleted) and `iend`, and finally pushing `nil`.  `outOrder` is the *push order* as a function
of the number `k` of bit positions already consumed. -/

/-- Delete the trailing `bit false` glyphs of a list. -/
def stripFalses (l : List Glyph) : List Glyph :=
  (l.reverse.dropWhile (fun g => g = Glyph.bit false)).reverse

/-- The gadget that pops the leading run of `bit false` glyphs of a stack (i.e. the trailing run of
the corresponding push order), stopping at the first other glyph. -/
def dropZerosProg (k : Stk) (r : Reg) : Cmd :=
  .seq (.peek k r) (.loop r (Glyph.bit false) (.seq (.pop k r) (.peek k r)))

/-- The push order of one complete group `j`: `cons`, `pos`, the canonical bits of the digit, `iend`. -/
def blk (ps : List Bool) (b j : ℕ) : List Glyph :=
  [Glyph.cons, Glyph.pos] ++ stripFalses (((ps.drop (b * j)).take b).map Glyph.bit) ++ [Glyph.iend]

/-- The push order of a group still in progress after `k` positions. -/
def partBlk (ps : List Bool) (b k : ℕ) : List Glyph :=
  [Glyph.cons, Glyph.pos] ++ (((ps.drop (b * (k / b))).take (k % b)).map Glyph.bit)

/-- The push order after `k` bit positions (excluding the final `nil`). -/
def outOrder (ps : List Bool) (b k : ℕ) : List Glyph :=
  List.flatMap (blk ps b) (List.range (k / b)) ++ (if k % b = 0 then [] else partBlk ps b k)

end Work.IntLib
