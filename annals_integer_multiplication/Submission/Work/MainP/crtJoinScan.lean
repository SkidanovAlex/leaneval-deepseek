import Mathlib
import Submission.Work.MainP.crtJoinDefs
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.dropValueLoopLe
import Submission.Work.Kernel.dropValueStk1PendStep

/-!
# `crtJoinElems`: the canonical states of the element scan

`Work.MainP.crtJoinElems` is about the program `Work.MainP.consumeListN dst cnt`
(`Submission/Work/MainP/crtJoinDefs.lean`), which copies the elements of a list of encodings from
stack 0, in reverse, onto the buffer stack `dst` while counting the glyphs of each element (one
`jtok` per glyph, blocks separated by `jdelim`) on the count stack `cnt`.

The copying of ONE element is `Work.MainP.scanVal dst cnt`: it is the Kernel's pending-subtree scan
(`Work.Kernel.dropValue_pre`, `Work.Kernel.dropValue_body`, `Work.Kernel.dropValue_iter`,
`Submission/Work/Kernel/dropValue*.lean`) with two extra pushes per round — the glyph read from
stack 0 is pushed on `dst` and one `jtok` is pushed on `cnt`.

This file fixes the canonical state of that scan: stack 0 holds the glyphs still to be read, `dst`
holds the already copied buffer, `cnt` the already pushed tokens, while stack 1 carries the unary
pending-subtree counter of the Kernel scan with `p` tokens above the (untouched) tail of stack 1 of
the ambient state `X`; registers 1, 2, 3 are the ones set by `Work.Kernel.dropValue_pre`.

Everything here is `sorry`-free and is meant to be imported by the files proving the `Eval`
behaviour of the individual loops.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## The canonical state of one element scan -/

/-- Canonical state of the element scan: stack 0 holds `l0` (the glyphs still to be read), the
unary pending-subtree counter on stack 1 has `p` tokens above `X.stk 1`, `dst` holds `B`, `cnt`
holds `C`, registers 1, 2, 3 are those of the Kernel scan (`dropValue_iter`) and every other
component is the one of `X`. -/
def scanSt (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ) : State :=
  ((Work.Kernel.dropValue_iter X l0 p).updStk dst B).updStk cnt C

@[simp] theorem scanSt_stk0 (X : State) (dst cnt : Stk) (h0d : dst ≠ 0) (h0c : cnt ≠ 0)
    (l0 B C : List Glyph) (p : ℕ) : (scanSt X dst cnt l0 B C p).stk 0 = l0 := by
  have h0d' : ¬ ((0 : Stk) = dst) := fun h => h0d h.symm
  have h0c' : ¬ ((0 : Stk) = cnt) := fun h => h0c h.symm
  simp [scanSt, h0d', h0c']

@[simp] theorem scanSt_stk_dst (X : State) (dst cnt : Stk) (hdc : dst ≠ cnt)
    (l0 B C : List Glyph) (p : ℕ) : (scanSt X dst cnt l0 B C p).stk dst = B := by
  simp [scanSt, hdc]

@[simp] theorem scanSt_stk_cnt (X : State) (dst cnt : Stk)
    (l0 B C : List Glyph) (p : ℕ) : (scanSt X dst cnt l0 B C p).stk cnt = C := by
  simp [scanSt]

@[simp] theorem scanSt_stk1 (X : State) (dst cnt : Stk) (h1d : dst ≠ 1) (h1c : cnt ≠ 1)
    (l0 B C : List Glyph) (p : ℕ) :
    (scanSt X dst cnt l0 B C p).stk 1 = Work.Kernel.dropValue_stk1 p (X.stk 1) := by
  have h1d' : ¬ ((1 : Stk) = dst) := fun h => h1d h.symm
  have h1c' : ¬ ((1 : Stk) = cnt) := fun h => h1c h.symm
  simp [scanSt, h1d', h1c']

theorem scanSt_stk_other (X : State) (dst cnt : Stk) (h0d : dst ≠ 0) (h0c : cnt ≠ 0)
    (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (l0 B C : List Glyph) (p : ℕ) (k : Stk)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hkd : k ≠ dst) (hkc : k ≠ cnt) :
    (scanSt X dst cnt l0 B C p).stk k = X.stk k := by
  have h1d' : ¬ ((1 : Stk) = dst) := fun h => h1d h.symm
  have h1c' : ¬ ((1 : Stk) = cnt) := fun h => h1c h.symm
  have h0d' : 0 ≠ dst := fun h => h0d h.symm
  simp only [scanSt, State.updStk_apply]
  rw [if_neg hkc, if_neg hkd]
  exact Work.Kernel.dropValue_iter_stk X l0 p k hk0 hk1

@[simp] theorem scanSt_reg1 (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ) :
    (scanSt X dst cnt l0 B C p).reg 1 =
      (if p = 0 then Work.Kernel.dropValue_base else Work.Kernel.dropValue_tok) := by
  simp [scanSt]

@[simp] theorem scanSt_reg2 (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ) :
    (scanSt X dst cnt l0 B C p).reg 2 = Work.Kernel.dropValue_base := by
  simp [scanSt]

@[simp] theorem scanSt_reg3 (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ) :
    (scanSt X dst cnt l0 B C p).reg 3 = Work.Kernel.dropValue_tok := by
  simp [scanSt]


@[simp] theorem scanSt_reg_other (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ)
    (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) :
    (scanSt X dst cnt l0 B C p).reg r = X.reg r := by
  simp only [scanSt, State.updStk_reg]
  exact Work.Kernel.dropValue_iter_reg X l0 p r h1 h2 h3

/-- `dropValue_iter X l0 p` is `scanSt X dst cnt l0 B C p` as soon as the two extra stacks already
carry `B` and `C` in the former. -/
theorem dropValue_iter_eq_scanSt (X : State) (dst cnt : Stk) (l0 B C : List Glyph) (p : ℕ)
    (hd : (Work.Kernel.dropValue_iter X l0 p).stk dst = B)
    (hc : (Work.Kernel.dropValue_iter X l0 p).stk cnt = C) :
    Work.Kernel.dropValue_iter X l0 p = scanSt X dst cnt l0 B C p := by
  rw [show B = (Work.Kernel.dropValue_iter X l0 p).stk dst from hd.symm,
    show C = (Work.Kernel.dropValue_iter X l0 p).stk cnt from hc.symm]
  simp [scanSt]

end Work.MainP
