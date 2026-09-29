import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Kernel.Raw

/-!
# IntLib: the `chunk` word — program, invariant, correctness

The `chunk` word reads the canonical bit encoding of `x < 2^(b*N)` off the value stack and builds
`intList (chunks x b N)` on a scratch stack, in `O(isz x + N*(b+1) + isz b + isz N)` steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Stack and register allocation -/

def sX : Stk := 3
def sB : Stk := 4
def sN : Stk := 5
def sR : Stk := 6
def sS : Stk := 7
def sCW : Stk := 8
def sCB : Stk := 9
def sCT : Stk := 10
def sCN : Stk := 11
def sZ : Stk := 12
def sT1 : Stk := 1
def sT2 : Stk := 2

def rG : Reg := 0
def rA : Reg := 1
def rB : Reg := 2
def rC_ch : Reg := 3
def rD : Reg := 4
def rE : Reg := 5
def rH : Reg := 6
def rK : Reg := 7

def gCont : Glyph := .mk 10
def gStop : Glyph := .mk 11

theorem gCont_ne_gStop : gCont ≠ gStop := by decide
theorem gCont_ne_gEnd : gCont ≠ gEnd := by decide
theorem gStop_ne_gEnd : gStop ≠ gEnd := by decide
theorem gStop_ne_gCont : gStop ≠ gCont := by decide
theorem gCont_ne_gTok : gCont ≠ gTok := by decide
theorem gStop_ne_gTok : gStop ≠ gTok := by decide
theorem gCont_ne_bit (b : Bool) : gCont ≠ Glyph.bit b := fun h => by cases h
theorem gStop_ne_bit (b : Bool) : gStop ≠ Glyph.bit b := fun h => by cases h

theorem gmk_ne_bit (k : Stk) (b : Bool) : Shift.gmk k ≠ Glyph.bit b := fun h => by cases h
theorem bit_ne_gmk (k : Stk) (b : Bool) : Glyph.bit b ≠ Shift.gmk k := fun h => by cases h
theorem gmk_ne_pos (k : Stk) : Shift.gmk k ≠ Glyph.pos := fun h => by cases h
theorem gmk_ne_iend (k : Stk) : Shift.gmk k ≠ Glyph.iend := fun h => by cases h
theorem gmk_ne_nil (k : Stk) : Shift.gmk k ≠ Glyph.nil := fun h => by cases h
theorem gmk_ne_cons (k : Stk) : Shift.gmk k ≠ Glyph.cons := fun h => by cases h
theorem pos_ne_gmk (k : Stk) : Glyph.pos ≠ Shift.gmk k := fun h => Shift.gmk_ne_pos k h.symm
theorem neg_ne_gmk (k : Stk) : Glyph.neg ≠ Shift.gmk k := fun h => Shift.gmk_ne_neg k h.symm
theorem iend_ne_gmk (k : Stk) : Glyph.iend ≠ Shift.gmk k := fun h => Shift.gmk_ne_iend k h.symm
theorem nil_ne_gmk (k : Stk) : Glyph.nil ≠ Shift.gmk k := fun h => Shift.gmk_ne_nil k h.symm
theorem cons_ne_gmk (k : Stk) : Glyph.cons ≠ Shift.gmk k := fun h => Shift.gmk_ne_cons k h.symm
theorem tok_ne_gmk {k : Stk} (h : k ≠ (14 : Stk)) : gTok ≠ Shift.gmk k := by
  intro hh
  exact h (by simpa [Shift.gmk, gTok] using hh.symm)
theorem end_ne_gmk {k : Stk} (h : k ≠ (13 : Stk)) : gEnd ≠ Shift.gmk k := by
  intro hh
  exact h (by simpa [Shift.gmk, gEnd] using hh.symm)
theorem cont_ne_gmk {k : Stk} (h : k ≠ (10 : Stk)) : gCont ≠ Shift.gmk k := by
  intro hh; exact h (by simpa [Shift.gmk, gCont] using hh.symm)
theorem stop_ne_gmk {k : Stk} (h : k ≠ (11 : Stk)) : gStop ≠ Shift.gmk k := by
  intro hh; exact h (by simpa [Shift.gmk, gStop] using hh.symm)
theorem bit_false_ne_cont : Glyph.bit false ≠ gCont := fun h => by cases h
theorem bit_false_ne_stop : Glyph.bit false ≠ gStop := fun h => by cases h
theorem bit_false_ne_tok : Glyph.bit false ≠ gTok := fun h => by cases h
theorem bit_false_ne_end : Glyph.bit false ≠ gEnd := fun h => by cases h

/-- No `Val` encoding contains a frame marker `gmk k`. -/
theorem noMark_enc (v : Val) : Shift.NoMark v.enc := by
  induction v with
  | int z =>
      intro g hg k
      simp only [Val.enc] at hg
      rcases List.mem_cons.mp hg with h | h
      · rw [h]
        by_cases hz : z < 0 <;> simp [hz, Shift.gmk]
      · rcases List.mem_append.mp h with h | h
        · exact Shift.noMark_bitsG _ g h k
        · rw [List.mem_singleton] at h
          rw [h]; simp [Shift.gmk]
  | nil => intro g hg k; simp only [Val.enc, List.mem_singleton] at hg; rw [hg]; simp [Shift.gmk]
  | cons a b iha ihb =>
      intro g hg k
      simp only [Val.enc, List.mem_cons] at hg
      rcases hg with h | h
      · rw [h]; simp [Shift.gmk]
      · rcases List.mem_append.mp h with h | h
        · exact iha g h k
        · exact ihb g h k

theorem noMark_enc_int (z : ℤ) : Shift.NoMark (Val.enc (.int z)) := noMark_enc _

theorem gmk_ne_of_ne {k j : Stk} (h : k ≠ j) : Shift.gmk k ≠ Shift.gmk j := by
  intro hh
  exact h (by simpa [Shift.gmk] using hh)

/-- The encodings of the three inputs are free of any frame marker. -/
theorem noMark_encs (x b N : ℕ) :
    Shift.NoMark (Val.enc (.int (x : ℤ)) ++ Val.enc (.int (b : ℤ)) ++
      Val.enc (.int (N : ℤ))) := by
  intro g hg k
  simp only [List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact noMark_enc_int _ g h k
  · exact noMark_enc_int _ g h k
  · exact noMark_enc_int _ g h k

/-! ## The bit stream, the padding, the counters and the loop state -/

/-- The bit encoding of `x` without its sign glyph: bits (low to high) then `iend`. -/
def streamOf (x : ℕ) : List Glyph := x.bits.map Glyph.bit ++ [Glyph.iend]

/-- The bits of `x` padded with zeros to length `b*N` (meaningful when `x < 2^(b*N)`). -/
def pbits (x b N : ℕ) : List Bool := x.bits ++ List.replicate (b * N - x.size) false

/-- Number of stream glyphs consumed after `k` positions. -/
def cg (x : ℕ) (k : ℕ) : ℕ := min k (x.size + 1)

/-- Number of units left in the working counter after `k` positions. -/
def wcnt (b k : ℕ) : ℕ := if k % b = 0 then 0 else b - k % b

/-- The stacks of the loop after `k` consumed bit positions. -/
def lStk (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) : Stk → List Glyph := fun j =>
  if j = sX then (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX
  else if j = sR then ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR
  else if j = sS then (outOrder (pbits x b N) b k).reverse ++ Shift.gmk sS :: Y sS
  else if j = sCW then Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)
  else if j = sCN then Unary (N - k / b) (Shift.gmk sCN :: Y sCN)
  else if j = sZ then Shift.gmk sZ :: Y sZ
  else Y j

/-- The register file of the loop after `k` consumed bit positions. -/
def lRegs (x b N : ℕ) (k : ℕ) : Reg → Glyph := fun r =>
  if r = rG then (if k < b * N then gCont else gStop) else Glyph.eos

/-- The state of the loop after `k` consumed bit positions. -/
def lSt (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) : State :=
  ⟨lRegs x b N k, lStk x b N Y k⟩

@[simp] theorem lSt_stk (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    (lSt x b N Y k).stk = lStk x b N Y k := rfl

@[simp] theorem lSt_reg (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    (lSt x b N Y k).reg = lRegs x b N k := rfl

@[simp] theorem lStk_sX (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sX = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX := by
  simp only [lStk, if_pos rfl, ↓reduceIte]

@[simp] theorem lStk_sR (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sR =
      ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR := by
  have h1 : ¬ (sR = sX) := by decide
  simp only [lStk, if_neg h1, if_pos rfl, ↓reduceIte]

@[simp] theorem lStk_sS (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sS = (outOrder (pbits x b N) b k).reverse ++ Shift.gmk sS :: Y sS := by
  have h1 : ¬ (sS = sX) := by decide
  have h2 : ¬ (sS = sR) := by decide
  simp only [lStk, if_neg h1, if_neg h2, if_pos rfl, ↓reduceIte]

@[simp] theorem lStk_sCW (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sCW = Unary (wcnt b k) (Shift.gmk sCW :: Y sCW) := by
  have h1 : ¬ (sCW = sX) := by decide
  have h2 : ¬ (sCW = sR) := by decide
  have h3 : ¬ (sCW = sS) := by decide
  simp only [lStk, if_neg h1, if_neg h2, if_neg h3, if_pos rfl, ↓reduceIte]

@[simp] theorem lStk_sCN (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
  have h1 : ¬ (sCN = sX) := by decide
  have h2 : ¬ (sCN = sR) := by decide
  have h3 : ¬ (sCN = sS) := by decide
  have h4 : ¬ (sCN = sCW) := by decide
  simp only [lStk, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos rfl, ↓reduceIte]

@[simp] theorem lStk_sZ (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) :
    lStk x b N Y k sZ = Shift.gmk sZ :: Y sZ := by
  have h1 : ¬ (sZ = sX) := by decide
  have h2 : ¬ (sZ = sR) := by decide
  have h3 : ¬ (sZ = sS) := by decide
  have h4 : ¬ (sZ = sCW) := by decide
  have h5 : ¬ (sZ = sCN) := by decide
  simp only [lStk, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos rfl, ↓reduceIte]

theorem lStk_other (x b N : ℕ) (Y : Stk → List Glyph) (k : ℕ) {j : Stk}
    (h1 : j ≠ sX) (h2 : j ≠ sR) (h3 : j ≠ sS) (h4 : j ≠ sCW) (h5 : j ≠ sCN) (h6 : j ≠ sZ) :
    lStk x b N Y k j = Y j := by
  simp only [lStk, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, ↓reduceIte]

@[simp] theorem lRegs_rG (x b N : ℕ) (k : ℕ) :
    lRegs x b N k rG = if k < b * N then gCont else gStop := by
  simp [lRegs]

theorem lRegs_other (x b N : ℕ) (k : ℕ) {r : Reg} (h : r ≠ rG) : lRegs x b N k r = Glyph.eos := by
  simp [lRegs, h]

/-! ## Arithmetic and list facts about the stream and the counters -/

theorem wcnt_eq_of_ne {b k : ℕ} (h : k % b ≠ 0) : wcnt b k = b - k % b := by
  unfold wcnt; rw [if_neg h]

theorem wcnt_eq_of_eq {b k : ℕ} (h : k % b = 0) : wcnt b k = 0 := by
  unfold wcnt; rw [if_pos h]

theorem wcnt_zero_iff {b k : ℕ} (hb : 1 ≤ b) : wcnt b k = 0 ↔ k % b = 0 := by
  by_cases h : k % b = 0
  · rw [wcnt_eq_of_eq h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [wcnt_eq_of_ne h]
    have h1 : k % b < b := Nat.mod_lt _ (by omega)
    constructor
    · intro hh; omega
    · intro hh; exact absurd hh h

theorem wcnt_pos {b k : ℕ} (hb : 1 ≤ b) (h : k % b ≠ 0) : 1 ≤ wcnt b k := by
  rw [wcnt_eq_of_ne h]
  have h1 : k % b < b := Nat.mod_lt _ (by omega)
  omega

theorem wcnt_succ_dec {b k : ℕ} (hb : 1 ≤ b) (h : k % b ≠ 0) :
    wcnt b (k + 1) = wcnt b k - 1 := by
  rcases Nat.lt_or_eq_of_le hb with hb2 | hb1
  · have h1 : 1 % b = 1 := Nat.mod_eq_of_lt hb2
    have hm : (k + 1) % b = (k % b + 1) % b := by rw [Nat.add_mod, h1]
    rw [wcnt_eq_of_ne h]
    by_cases hc : k % b + 1 = b
    · have hm0 : (k + 1) % b = 0 := by rw [hm, hc, Nat.mod_self]
      rw [wcnt_eq_of_eq hm0]
      omega
    · have hlt' : k % b + 1 < b := by
        have := Nat.mod_lt k (by omega : 0 < b); omega
      have hm1 : (k + 1) % b = k % b + 1 := by rw [hm, Nat.mod_eq_of_lt hlt']
      rw [wcnt_eq_of_ne (by rw [hm1]; omega), hm1]
      omega
  · subst hb1; exact absurd (Nat.mod_one k) h

theorem wcnt_succ_open {b k : ℕ} (hb : 1 ≤ b) (h : k % b = 0) : wcnt b (k + 1) = b - 1 := by
  rcases Nat.lt_or_eq_of_le hb with hb2 | hb1
  · have h1 : 1 % b = 1 := Nat.mod_eq_of_lt hb2
    have hm : (k + 1) % b = 1 := by rw [Nat.add_mod, h, h1, Nat.zero_add, h1]
    rw [wcnt_eq_of_ne (by rw [hm]; omega), hm]
  · subst hb1
    rw [wcnt_eq_of_eq (Nat.mod_one (k + 1))]

theorem cg_of_lt {x k : ℕ} (h : k < x.size) : cg x k = k := by
  unfold cg; exact Nat.min_eq_left (by omega)
theorem cg_of_eq (x : ℕ) : cg x x.size = x.size := by
  unfold cg; exact Nat.min_eq_left (by omega)
theorem cg_of_gt {x k : ℕ} (h : x.size < k) : cg x k = x.size + 1 := by
  unfold cg; exact Nat.min_eq_right (by omega)
theorem cg_succ {x k : ℕ} (h : k ≤ x.size) : cg x (k + 1) = cg x k + 1 := by
  unfold cg; rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
theorem cg_succ_gt {x k : ℕ} (h : x.size < k) : cg x (k + 1) = cg x k := by
  rw [cg_of_gt h, cg_of_gt (by omega)]
theorem cg_le (x k : ℕ) : cg x k ≤ x.size + 1 := by
  unfold cg; exact Nat.min_le_right _ _

theorem streamOf_length (x : ℕ) : (streamOf x).length = x.size + 1 := by
  unfold streamOf
  rw [List.length_append, List.length_map, List.length_singleton, Nat.size_eq_bits_len]

theorem streamOf_getD_lt {x k : ℕ} (h : k < x.size) :
    (streamOf x).getD k Glyph.eos = Glyph.bit (x.bits.getD k false) := by
  unfold streamOf
  have hlen : (x.bits.map Glyph.bit).length = x.size := by
    rw [List.length_map, Nat.size_eq_bits_len]
  have h1 : k < (x.bits.map Glyph.bit ++ [Glyph.iend]).length := by
    rw [List.length_append, hlen, List.length_singleton]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getElem_append_left (by rw [hlen]; exact h),
    List.getElem_map, List.getD_eq_getElem _ _ (by rw [Nat.size_eq_bits_len]; exact h)]

theorem streamOf_drop_lt {x k : ℕ} (h : k < x.size) :
    (streamOf x).drop k = Glyph.bit (x.bits.getD k false) :: (streamOf x).drop (k + 1) := by
  have hlen : (x.bits.map Glyph.bit).length = x.size := by
    rw [List.length_map, Nat.size_eq_bits_len]
  have hp1 : k ≤ (x.bits.map Glyph.bit).length := by rw [hlen]; omega
  have hp2 : k + 1 ≤ (x.bits.map Glyph.bit).length := by rw [hlen]; omega
  have h2 : k < (x.bits.map Glyph.bit).length := by rw [hlen]; omega
  unfold streamOf
  rw [List.drop_append_of_le_length hp1, List.drop_append_of_le_length hp2,
      List.drop_eq_getElem_cons h2, List.getElem_map,
      List.getD_eq_getElem _ _ (by rw [Nat.size_eq_bits_len]; exact h)]
  simp only [List.cons_append]

theorem streamOf_drop_eq (x : ℕ) : (streamOf x).drop (cg x x.size) = [Glyph.iend] := by
  rw [cg_of_eq]
  unfold streamOf
  have hlen : (x.bits.map Glyph.bit).length = x.size := by
    rw [List.length_map, Nat.size_eq_bits_len]
  rw [List.drop_append_of_le_length (by rw [hlen]), List.drop_eq_nil_of_le (by rw [hlen])]
  simp

theorem streamOf_drop_gt {x k : ℕ} (h : x.size < k) : (streamOf x).drop k = [] := by
  unfold streamOf
  have hlen : (x.bits.map Glyph.bit).length = x.size := by
    rw [List.length_map, Nat.size_eq_bits_len]
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (by rw [hlen]; omega)]
  simp only [List.nil_append]
  rw [List.drop_eq_nil_of_le (by simp [Nat.size_eq_bits_len]; omega)]

theorem pbits_length {x b N : ℕ} (h : x.size ≤ b * N) : (pbits x b N).length = b * N := by
  unfold pbits
  rw [List.length_append, List.length_replicate, Nat.size_eq_bits_len]
  omega

theorem pbits_getD_lt {x b N k : ℕ} (hk : k < x.size) :
    (pbits x b N).getD k false = x.bits.getD k false := by
  unfold pbits
  have h1 : k < (x.bits ++ List.replicate (b * N - x.size) false).length := by
    rw [List.length_append, List.length_replicate, Nat.size_eq_bits_len]; omega
  rw [List.getD_eq_getElem _ _ h1,
      List.getD_eq_getElem _ _ (by rw [Nat.size_eq_bits_len]; exact hk),
      List.getElem_append_left (by rw [Nat.size_eq_bits_len]; exact hk)]

theorem pbits_getD_ge {x b N k : ℕ} (hk : x.size ≤ k) :
    (pbits x b N).getD k false = false := by
  unfold pbits
  by_cases hb : k < b * N
  · have h1 : k < (x.bits ++ List.replicate (b * N - x.size) false).length := by
      rw [List.length_append, List.length_replicate, Nat.size_eq_bits_len]; omega
    rw [List.getD_eq_getElem _ _ h1,
        List.getElem_append_right (by rw [Nat.size_eq_bits_len]; exact hk),
        List.getElem_replicate]
  · have h1 : (x.bits ++ List.replicate (b * N - x.size) false).length ≤ k := by
      rw [List.length_append, List.length_replicate, Nat.size_eq_bits_len]; omega
    rw [List.getD_eq_default _ _ h1]

/-- The bit at position `k` of the padded stream is the canonical bit of `x` for `k < x.size`. -/
theorem pbits_getD_of_lt {x b N k : ℕ} (hk : k < x.size) :
    Glyph.bit ((pbits x b N).getD k false) = Glyph.bit (x.bits.getD k false) := by
  rw [pbits_getD_lt hk]

theorem headD_drop (l : List Glyph) (n : ℕ) :
    (l.drop n).headD Glyph.eos = l.getD n Glyph.eos := by
  induction l generalizing n with
  | nil => simp
  | cons h t ih => cases n <;> simp [ih]

theorem streamOf_head_lt {b N x k : ℕ} (h : k < x.size) :
    ((streamOf x).drop (cg x k)).headD Glyph.eos = Glyph.bit ((pbits x b N).getD k false) := by
  rw [cg_of_lt h, headD_drop, streamOf_getD_lt h, pbits_getD_of_lt h]

theorem streamOf_head_eq (x : ℕ) :
    ((streamOf x).drop (cg x x.size)).headD Glyph.eos = Glyph.iend := by
  rw [streamOf_drop_eq]; rfl

theorem streamOf_take_succ_lt {b N x k : ℕ} (h : k < x.size) :
    (streamOf x).take (cg x (k + 1)) =
      (streamOf x).take (cg x k) ++ [Glyph.bit ((pbits x b N).getD k false)] := by
  rw [cg_succ (le_of_lt h), cg_of_lt h,
      List.take_succ_eq_append_getElem (by rw [streamOf_length]; omega),
      ← List.getD_eq_getElem _ _ (by rw [streamOf_length]; omega),
      streamOf_getD_lt h, pbits_getD_of_lt h]

theorem streamOf_take_eq (x : ℕ) : (streamOf x).take x.size = x.bits.map Glyph.bit := by
  unfold streamOf
  rw [List.take_append_of_le_length (by rw [List.length_map, Nat.size_eq_bits_len]),
      List.take_of_length_le (by rw [List.length_map, Nat.size_eq_bits_len])]

theorem streamOf_take_succ_eq (x : ℕ) :
    (streamOf x).take (cg x (x.size + 1)) =
      (streamOf x).take (cg x x.size) ++ [Glyph.iend] := by
  rw [cg_succ (le_refl x.size), cg_of_eq, streamOf_take_eq,
      List.take_of_length_le (by rw [streamOf_length])]
  rfl

theorem streamOf_take_succ_gt {x k : ℕ} (h : x.size < k) :
    (streamOf x).take (cg x (k + 1)) = (streamOf x).take (cg x k) := by
  rw [cg_succ_gt h, cg_of_gt h]

/-- The cost bound of one iteration of the main loop. -/
def cstep (b KC k : ℕ) : ℕ :=
  100 + (if k % b = 0 then KC * (b + 1) else 0) + (if (k + 1) % b = 0 then 3 * b + 30 else 0)

/-- Set every register to `eos`. -/
def resetRegs : Cmd := seqs ((List.finRange 16).map fun r => Cmd.set r Glyph.eos)

/-- The body of the main loop: consume one bit position. -/
def loopBody (copyProg : Cmd) : Cmd :=
  seqs [
    .peek sX rA,
    .ite rA (Shift.gmk sX)
        (.set rA (Glyph.bit false))
        (.seq (.pop sX rA)
          (.ite rA Glyph.iend
            (.seq (.push sR rA) (.set rA (Glyph.bit false)))
            (.push sR rA))),
    .push sZ rA,
    .peek sCW rB,
    .ite rB gEnd
        (seqs [.set rC_ch Glyph.cons, .push sS rC_ch, .set rC_ch Glyph.pos, .push sS rC_ch, .set rE gCont])
        (.set rE gStop),
    .ite rE gCont copyProg .skip,
    .pop sZ rA,
    .push sS rA,
    .pop sCW rB,
    .peek sCW rB,
    .ite rB gEnd
        (seqs [dropZerosProg sS rD, .set rC_ch Glyph.iend, .push sS rC_ch, .pop sCN rB])
        .skip,
    resetRegs,
    .peek sCN rG,
    .ite rG gEnd (.set rG gStop) (.set rG gCont)]

theorem setAll_ev (main : Cmd) (l : List Reg) (s : State) :
    ∃ (s' : State) (n : ℕ), Ev main (seqs (l.map fun r => Cmd.set r Glyph.eos)) s s' n ∧
      n ≤ l.length + 1 ∧ (∀ r ∈ l, s'.reg r = Glyph.eos) ∧ s'.stk = s.stk ∧
      (∀ r, r ∉ l → s'.reg r = s.reg r) := by
  induction l generalizing s with
  | nil => exact ⟨s, 1, Ev.seqs_nil, by simp, by simp, rfl, by intro r _; rfl⟩
  | cons a t ih =>
    obtain ⟨s1, n1, h1, hn1, hreg1, hstk1, hoth1⟩ := ih (State.tSet s a Glyph.eos)
    have hset : Ev main (Cmd.set a Glyph.eos) s (State.tSet s a Glyph.eos) 1 :=
      ⟨1, Eval.set a Glyph.eos s, le_rfl⟩
    have hseq : Ev main (seqs ((a :: t).map fun r => Cmd.set r Glyph.eos)) s s1 (1 + n1) := by
      rw [List.map_cons]
      exact Ev.seqs_cons hset h1
    refine ⟨s1, 1 + n1, hseq, by simp; omega, ?_, ?_, ?_⟩
    · intro r hr
      have hr' : r = a ∨ r ∈ t := by simpa [List.mem_cons] using hr
      rcases hr' with h | h
      · rw [h]
        by_cases hat : a ∈ t
        · exact hreg1 a hat
        · rw [hoth1 a hat]; simp [State.tSet]
      · exact hreg1 r h
    · rw [hstk1]; rfl
    · intro r hr
      have hra : r ≠ a := fun h => hr (by rw [← h]; exact List.mem_cons_self)
      have hrt : r ∉ t := fun hc => hr (List.mem_cons_of_mem a hc)
      rw [hoth1 r hrt, State.tSet, State.updReg_apply, if_neg hra]

theorem resetRegs_ev (main : Cmd) (s : State) :
    ∃ (s' : State) (n : ℕ), Ev main resetRegs s s' n ∧ n ≤ 17 ∧
      (∀ r : Reg, s'.reg r = Glyph.eos) ∧ s'.stk = s.stk := by
  obtain ⟨s', n, h1, hn, hreg, hstk, -⟩ :=
    setAll_ev main (List.finRange 16) s
  refine ⟨s', n, ?_, by simpa using hn, fun r => hreg r (List.mem_finRange r), hstk⟩
  simpa [resetRegs] using h1

/-! ## The main loop -/

/-- Partial sums of the per-iteration cost bound (including the loop test). -/
def lsum (b KC : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lsum b KC k + (cstep b KC k + 1)

/-- Set the loop flag and run the main loop. -/
def loopProg (copyProg : Cmd) : Cmd := .seq (.set rG gCont) (.loop rG gCont (loopBody copyProg))

/-- The loop runs `b*N` iterations. -/
theorem loopRuns_lSt (main : Cmd) (copyProg : Cmd) (KC : ℕ) (Ca : List Glyph)
    (hstep : ∀ (x b N : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N)) (Y : Stk → List Glyph),
      Y sCB = Unary b Ca → ∀ k, k < b * N →
        Ev main (loopBody copyProg) (lSt x b N Y k) (lSt x b N Y (k + 1)) (cstep b KC k))
    (x b N : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N)) (Y : Stk → List Glyph)
    (hCB : Y sCB = Unary b Ca) :
    ∀ k, k ≤ b * N →
      loopRuns main rG gCont (loopBody copyProg) k (lSt x b N Y 0) (lSt x b N Y k) (lsum b KC k) := by
  intro k
  induction k with
  | zero => intro _; exact loopRuns.zero
  | succ k ih =>
    intro hk
    have hk' : k < b * N := by omega
    have ihm := ih (by omega)
    have hreg : (lSt x b N Y k).reg rG = gCont := by
      rw [lSt_reg, lRegs_rG]; simp [hk']
    have hbody := hstep x b N hb hxN Y hCB k hk'
    have hone : loopRuns main rG gCont (loopBody copyProg) 1 (lSt x b N Y k) (lSt x b N Y (k + 1))
        (cstep b KC k + 1) := loopRuns.one hreg hbody
    have hcat := loopRuns.concat 1 ihm hone
    simpa only [lsum] using hcat

/-- The whole loop, from the entry state to the exit state. -/
theorem loop_ev (main : Cmd) (copyProg : Cmd) (KC : ℕ) (Ca : List Glyph)
    (hstep : ∀ (x b N : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N)) (Y : Stk → List Glyph),
      Y sCB = Unary b Ca → ∀ k, k < b * N →
        Ev main (loopBody copyProg) (lSt x b N Y k) (lSt x b N Y (k + 1)) (cstep b KC k))
    (x b N : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N)) (hpos : 0 < b * N)
    (Y : Stk → List Glyph) (hCB : Y sCB = Unary b Ca)
    (g : Reg → Glyph) (hg : ∀ r, r ≠ rG → g r = Glyph.eos) :
    Ev main (loopProg copyProg) ⟨g, lStk x b N Y 0⟩ (lSt x b N Y (b * N))
      (1 + (lsum b KC (b * N) + 1)) := by
  have hrun := loopRuns_lSt main copyProg KC Ca hstep x b N hb hxN Y hCB (b * N) le_rfl
  have hne : (lSt x b N Y (b * N)).reg rG ≠ gCont := by
    rw [lSt_reg, lRegs_rG]
    simp only [if_neg (by omega : ¬ b * N < b * N)]
    exact gStop_ne_gCont
  obtain ⟨n, hev, hle⟩ := loopRuns.eval' hrun hne
  have hupd : Function.update g rG gCont = lRegs x b N 0 := by
    funext r
    by_cases hr : r = rG
    · subst hr; rw [Function.update_self, lRegs_rG]; simp [hpos]
    · rw [Function.update_of_ne hr, hg r hr, lRegs_other x b N 0 hr]
  have hset : Ev main (.set rG gCont) ⟨g, lStk x b N Y 0⟩ (lSt x b N Y 0) 1 := by
    have h0 := Eval.set (main := main) rG gCont (⟨g, lStk x b N Y 0⟩ : State)
    have hstate : (⟨Function.update g rG gCont, lStk x b N Y 0⟩ : State) = lSt x b N Y 0 := by
      simp only [hupd, lSt]
    rw [hstate] at h0
    exact ⟨1, h0, le_rfl⟩
  obtain ⟨n1, he1, hn1⟩ := hset
  exact ⟨n1 + n, Eval.seq he1 hev, by omega⟩

/-! ## The pre-phase -/

/-- The initial stack function: stack 0 holds the three inputs above `X₀ 0`. -/
def Xinit (x b N : ℕ) (X₀ : Stk → List Glyph) : Stk → List Glyph := fun j =>
  if j = 0 then Val.enc (.int (x : ℤ)) ++ Val.enc (.int (b : ℤ)) ++ Val.enc (.int (N : ℤ)) ++ X₀ 0
  else X₀ j

/-- The loop-entry stack function (the "below" contents of the loop invariant). -/
def Yinit (b N : ℕ) (X₀ : Stk → List Glyph) : Stk → List Glyph := fun j =>
  if j = sB then Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB
  else if j = sN then Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN
  else if j = sCB then Unary b (Shift.gmk sCB :: X₀ sCB)
  else if j = sCT then Shift.gmk sCT :: X₀ sCT
  else X₀ j

@[simp] theorem Yinit_sB (b N : ℕ) (X₀ : Stk → List Glyph) :
    Yinit b N X₀ sB = Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := by simp [Yinit]

@[simp] theorem Yinit_sN (b N : ℕ) (X₀ : Stk → List Glyph) :
    Yinit b N X₀ sN = Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := by
  have h : ¬ (sN = sB) := by decide
  simp only [Yinit, if_neg h, if_pos rfl, ↓reduceIte]

@[simp] theorem Yinit_sCB (b N : ℕ) (X₀ : Stk → List Glyph) :
    Yinit b N X₀ sCB = Unary b (Shift.gmk sCB :: X₀ sCB) := by
  have h1 : ¬ (sCB = sB) := by decide
  have h2 : ¬ (sCB = sN) := by decide
  simp only [Yinit, if_neg h1, if_neg h2, if_pos rfl, ↓reduceIte]

@[simp] theorem Yinit_other (b N : ℕ) (X₀ : Stk → List Glyph) {j : Stk}
    (h1 : j ≠ sB) (h2 : j ≠ sN) (h3 : j ≠ sCB) (h4 : j ≠ sCT) : Yinit b N X₀ j = X₀ j := by
  simp only [Yinit, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- Push the frame marker of stack `k`. -/
def mkStep (k : Stk) (r : Reg) : Cmd := .seq (.set r (Shift.gmk k)) (.push k r)

/-- The setup shared by both branches: markers, the three moves, the `N` counter. -/
def preSetupProg (rebuildN : Cmd) : Cmd :=
  seqs [mkStep sX rH, mkStep sB rH, mkStep sN rH, mkStep sR rH, mkStep sS rH,
        mkStep sCW rH, mkStep sCB rH, mkStep sCT rH, mkStep sCN rH, mkStep sZ rH,
        .set rH gEnd, .push sCW rH,
        Work.Layout.mvVal 0 sX sT1 sT2, Work.Layout.mvVal 0 sB sT1 sT2,
        Work.Layout.mvVal 0 sN sT1 sT2,
        Shift.drain sN sR (Shift.gmk sN) rH rK, rebuildN]

/-- The branch taken when `N ≠ 0`: setup of the `b` counter, the `x` stream, and the loop. -/
def preMainProg (rebuildB : Cmd) (loopP : Cmd) : Cmd :=
  seqs [Shift.drain sB sR (Shift.gmk sB) rH rK, rebuildB,
        .pop sX rA, .push sR rA, resetRegs, loopP]

/-- The stacks the post-phase clears. -/
def clearList : List Stk := [sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ]

/-- The post-phase proper (after the branch). -/
def postProg : Cmd :=
  .seq (seqs [.set rH Glyph.nil, .push sS rH])
    (.seq (Shift.drain sS 0 (Shift.gmk sS) rH rK)
      (seqs (clearList.map fun k => Shift.clearAll k rH rK)))

/-- The complete `chunk` word. -/
def chunkProg (copyProg rebuildN rebuildB : Cmd) : Cmd :=
  seqs [preSetupProg rebuildN, .peek sCN rC_ch,
        .ite rC_ch gEnd .skip (preMainProg rebuildB (loopProg copyProg)), postProg]
-- The pre-phase, the cell phase and the post-phase are proved in the sibling modules
-- `preSetupPhase.lean`, `preMainPhaseV2.lean` and `postPhase/postPhase.lean`, which import
-- this file for the definitions below.
end Work.IntLib

