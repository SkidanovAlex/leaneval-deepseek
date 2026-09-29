import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw

/-!
# ConvR: the "trivial array" flag word (`Work.ConvR.flagWord`)

Given `[int p, int c, rarrVal As] ++ rest` on the value stack, with `InDiscArr p M r As`,
push `int 0` if every entry of `As` is the empty vector and `int 1` otherwise.

Under `InDiscArr` all entries of `As` have the same length `r`, so the flag is decided by the
first two glyphs of the array encoding:

* `rarrVal []        = nil`,                    so the head is `nil`;
* `rarrVal (w :: ws) = cons (cvecVal w) (rarrVal ws)`, so the head is `cons`, and the next glyph
  is the head of `cvecVal w`, which is `nil` exactly when `w = []`.

The two integer encodings in front of the array have to be *restored*, so the program reads them
onto a scratch stack (stack 1), delimited by the frame marker `Glyph.mk 3`, decides the flag into
register `2` (`pos` = 0, `neg` = 1), restores the two encodings (and, in the `cons` case, the
glyph it consumed) from the scratch stack, and finally pushes the flag value.

Registers: `0` = loop flag (`mk 1` = continue, `mk 2` = stop), `1` = glyph register,
`2` = decision, `3` = marker register, `4` = scratch for `pushGlyphs`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Body of the "read one encoded value, remembering it on stack `rd`" loop: pop a glyph from
`rs`, push it on `rd`, and stop (set the loop flag to `mk 2`) once the glyph read is `iend`. -/
def readBody (rs rd : Stk) (rf rv : Reg) : Cmd :=
  Cmd.seq (Cmd.pop rs rv)
    (Cmd.seq (Cmd.push rd rv)
      (Cmd.ite rv Glyph.iend (Cmd.set rf (Glyph.mk 2)) Cmd.skip))

/-- The read loop (loop flag `rf` is set to `mk 1` first). -/
def readLoop (rs rd : Stk) (rf rv : Reg) : Cmd :=
  Cmd.seq (Cmd.set rf (Glyph.mk 1)) (Cmd.loop rf (Glyph.mk 1) (readBody rs rd rf rv))

/-- Body of the restore loop: pop a glyph from `rs`; if it is the frame marker `m`, stop,
otherwise push it on `rd`. -/
def restBody (rs rd : Stk) (rf rv : Reg) (m : Glyph) : Cmd :=
  Cmd.seq (Cmd.pop rs rv) (Cmd.ite rv m (Cmd.set rf (Glyph.mk 2)) (Cmd.push rd rv))

/-- The restore loop (loop flag `rf` is set to `mk 1` first). -/
def restLoop (rs rd : Stk) (rf rv : Reg) (m : Glyph) : Cmd :=
  Cmd.seq (Cmd.set rf (Glyph.mk 1)) (Cmd.loop rf (Glyph.mk 1) (restBody rs rd rf rv m))

/-- Read the first two glyphs of the array encoding into register `2`: `pos` for the all-empty
case, `neg` for the not-all-empty case.  Only the first glyph is consumed (only in the `cons` case,
and it is remembered on stack 1 for the restoration); the second glyph is only peeked. -/
def flagDecide : Cmd :=
  Cmd.seq (Cmd.peek 0 1)
    (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos)
      (Cmd.ite 1 Glyph.cons
        (Cmd.seq (Cmd.push 1 1)
          (Cmd.seq (Cmd.pop 0 1)
            (Cmd.seq (Cmd.peek 0 1)
              (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
        (Cmd.set 2 Glyph.pos)))

/-- Push the integer value `k` on top of stack 0, using register `scr` as scratch. -/
def pushIntVal (k : ℕ) (scr : Reg) : Cmd :=
  Work.Kernel.pushGlyphs ((Val.int (k : ℤ)).enc.reverse) 0 scr

/-- The complete flag word. -/
def flagProg : Cmd :=
  Cmd.seq (Cmd.seq (Cmd.set 3 (Glyph.mk 3)) (Cmd.push 1 3))
    (Cmd.seq (readLoop 0 1 0 1)
      (Cmd.seq (readLoop 0 1 0 1)
        (Cmd.seq flagDecide
          (Cmd.seq (restLoop 1 0 0 1 (Glyph.mk 3))
            (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4))))))

/-! ## State helpers -/

namespace FlagAux

/-- Two states are equal if they agree on every stack and every register. -/
theorem State.ext_stk_reg {s t : State} (h1 : ∀ k, s.stk k = t.stk k)
    (h2 : ∀ r, s.reg r = t.reg r) : s = t := by
  cases s with
  | mk reg stk =>
  cases t with
  | mk reg' stk' =>
    simp only [State.mk.injEq]
    exact ⟨funext h2, funext h1⟩

/-- The two stack updates commute. -/
theorem State.updStk_comm (s : State) (k k' : Stk) (l l' : List Glyph) (h : k ≠ k') :
    (s.updStk k l).updStk k' l' = (s.updStk k' l').updStk k l := by
  cases s with
  | mk reg stk =>
    simp only [State.updStk]
    congr 1
    exact Function.update_comm h l l' stk

end FlagAux

/-! ## The final states of the two loops -/

/-- State reached by `readLoop rs rd rf rv` when the stack `rs` starts with `l₁ ++ [iend]`:
those glyphs (reversed) are moved to `rd` and the register `rv` holds `iend`. -/
def readFin (rs rd : Stk) (rv : Reg) (l₁ l₂ : List Glyph) (s : State) : State :=
  (((s.updStk rs l₂).updReg rv Glyph.iend).updStk rd ((l₁ ++ [Glyph.iend]).reverse ++ s.stk rd))

/-- State reached by `restLoop rs rd rf rv m` when the stack `rs` starts with `B ++ [m]`:
the glyphs of `B` (reversed) are moved to `rd`, the marker `m` is dropped and `rv` holds `m`. -/
def restFin (rs rd : Stk) (rv : Reg) (m : Glyph) (B l₀ : List Glyph) (s : State) : State :=
  (((s.updStk rs l₀).updReg rv m).updStk rd (B.reverse ++ s.stk rd))

/-! ## The encoded integer prefix -/

/-- The integer encoding without its trailing `iend`. -/
def intBody (z : ℤ) : List Glyph :=
  (if z < 0 then Glyph.neg else Glyph.pos) :: (Computability.encodeNat z.natAbs).map Glyph.bit

theorem intEnc_eq (z : ℤ) : (Val.int z).enc = intBody z ++ [Glyph.iend] := rfl

theorem intEnc_length (z : ℤ) : (Val.int z).enc.length = isz z := Work.ConvR.vsz_int z

theorem iend_notMem_intBody (z : ℤ) : Glyph.iend ∉ intBody z := by
  rw [intBody, List.mem_cons, List.mem_map]
  rintro (h | ⟨b, _, hb⟩)
  · split at h <;> exact absurd h (by decide)
  · cases hb

theorem intBody_length (z : ℤ) : (intBody z).length + 1 = isz z := by
  have h := intEnc_length z
  rw [intEnc_eq] at h
  simp at h
  omega

/-! ## Encoding arithmetic -/

theorem encs_three (a b c : Val) (rest : List Val) (R : List Glyph) :
    encs (a :: b :: c :: rest) ++ R = a.enc ++ (b.enc ++ (c.enc ++ (encs rest ++ R))) := by
  simp [Work.Kernel.encs_cons, List.append_assoc]

/-! ## The three possible outcomes of `flagDecide`

Register `2` receives `pos` ("flag 0") in the two empty cases and `neg` ("flag 1") otherwise. -/

/-- Outcome of `flagDecide` when the top glyph is `nil` (the array is empty): nothing is consumed. -/
def flagNilOut (s : State) : State := (s.updReg 1 Glyph.nil).updReg 2 Glyph.pos

/-- First step of the `cons` branch: the peeked `cons` glyph. -/
def fdP (s : State) : State := s.updReg 1 Glyph.cons

/-- Second step of the `cons` branch: the `cons` glyph is pushed on the scratch stack. -/
def fdQ (s : State) : State := (fdP s).updStk 1 (Glyph.cons :: s.stk 1)

/-- Third step: the `cons` glyph is popped from stack 0. -/
def fdR (s : State) (g : Glyph) (T : List Glyph) : State :=
  ((fdQ s).updStk 0 (g :: T)).updReg 1 Glyph.cons

/-- Fourth step: the second glyph `g` of the array encoding is peeked. -/
def fdS (s : State) (g : Glyph) (T : List Glyph) : State := (fdR s g T).updReg 1 g

/-- Outcome of `flagDecide` when the array starts with `cons` and the next glyph is `nil`
(the first row is empty): the `cons` glyph goes to stack 1 and is removed from stack 0. -/
def flagRowNilOut (s : State) (T : List Glyph) : State := (fdS s Glyph.nil T).updReg 2 Glyph.pos

/-- Outcome of `flagDecide` when the array starts with `cons` and the next glyph is not `nil`
(the first row is non-empty): the `cons` glyph goes to stack 1 and is removed from stack 0. -/
def flagRowConsOut (s : State) (g : Glyph) (T : List Glyph) : State :=
  (fdS s g T).updReg 2 Glyph.neg

/-! ## Reading off the components of the loop end states -/

theorem readFin_stk_rs {rs rd : Stk} (hrd : rd ≠ rs) (rv : Reg) (l₁ l₂ : List Glyph) (s : State) :
    (readFin rs rd rv l₁ l₂ s).stk rs = l₂ := by
  have hrs : rs ≠ rd := fun h => hrd h.symm
  simp only [readFin, State.updStk_apply, State.updReg_stk, hrs, ↓reduceIte, State.updStk_same]

theorem readFin_stk_rd {rs rd : Stk} (hrd : rd ≠ rs) (rv : Reg) (l₁ l₂ : List Glyph) (s : State) :
    (readFin rs rd rv l₁ l₂ s).stk rd = (l₁ ++ [Glyph.iend]).reverse ++ s.stk rd := by
  simp only [readFin, State.updStk_apply, State.updReg_stk, State.updStk_same, if_true]

theorem readFin_stk_ne {rs rd : Stk} (rv : Reg) (l₁ l₂ : List Glyph) (s : State) {k : Stk}
    (h1 : k ≠ rs) (h2 : k ≠ rd) :
    (readFin rs rd rv l₁ l₂ s).stk k = s.stk k := by
  simp only [readFin, State.updStk_apply, State.updReg_stk, h1, h2, ↓reduceIte]

theorem restFin_stk_rs {rs rd : Stk} (hrd : rd ≠ rs) (rv : Reg) (m : Glyph) (B l₀ : List Glyph)
    (s : State) : (restFin rs rd rv m B l₀ s).stk rs = l₀ := by
  have hrs : rs ≠ rd := fun h => hrd h.symm
  simp only [restFin, State.updStk_apply, State.updReg_stk, hrs, ↓reduceIte, State.updStk_same]

theorem restFin_stk_rd {rs rd : Stk} (hrd : rd ≠ rs) (rv : Reg) (m : Glyph) (B l₀ : List Glyph)
    (s : State) : (restFin rs rd rv m B l₀ s).stk rd = B.reverse ++ s.stk rd := by
  simp only [restFin, State.updStk_apply, State.updReg_stk, State.updStk_same, if_true]

theorem restFin_stk_ne {rs rd : Stk} (rv : Reg) (m : Glyph) (B l₀ : List Glyph) (s : State)
    {k : Stk} (h1 : k ≠ rs) (h2 : k ≠ rd) :
    (restFin rs rd rv m B l₀ s).stk k = s.stk k := by
  simp only [restFin, State.updStk_apply, State.updReg_stk, h1, h2, ↓reduceIte]

end Work.ConvR
