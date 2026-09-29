import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Basic

/-!
# `IntLib` / add–sub: specification of the simultaneous subtractor `asw_subLoop`

`asw_subLoop a b o1 o2` ripples through the two marked bit lists on `a` and `b` (least
significant digit first) and pushes, simultaneously, the digits of `|a| - |b|` on `o1` and
those of `|b| - |a|` on `o2`; the final borrows are left in the registers `rC`, `rD`.

The main theorem `asw_subLoop_spec` states the resulting `ofBits` identities: if `e1`, `e2`
are the emitted digit lists and `bw1`, `bw2` the final borrows, then (over `ℤ`)

`ofBits e1 = ofBits ra - ofBits rb + 2 ^ e1.length * bw1.toNat`   (and symmetrically for `e2`),

with cost `≤ 31 * (ra.length + rb.length + 2)`.

The proof is layered:

* `asw_leaf_ev` — the leaf `asw_leaf` (emit a bit, set the borrow register);
* `asw_subTree_ev` — the 8-case decision tree `asw_subTree`;
* `asw_subBody_ev` — one iteration of the loop;
* `asw_subLoop_loop_ev` — the loop, by induction on `ra.length + rb.length`;
* `asw_subLoop_spec` — the three initialisations followed by the loop.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## Arithmetic of one subtractor digit -/

/-- One digit of the subtraction `x - y - c` (two's complement) and the outgoing borrow
satisfy `x - y - c = out - 2 * borrow`. -/
theorem asw_sub_digit_key (x y c : Bool) :
    ((asw_subOutBit x y c).toNat : ℤ) - 2 * ((asw_subBw x y c).toNat : ℤ)
      = (x.toNat : ℤ) - (y.toNat : ℤ) - (c.toNat : ℤ) := by
  cases x <;> cases y <;> cases c <;> decide

/-- `ofBits xs` minus twice `ofBits xs.tail` is the first digit of `xs` (`false` for `[]`). -/
theorem ofBits_head (xs : List Bool) :
    (ofBits xs : ℤ) - 2 * (ofBits xs.tail : ℤ) = ((xs.headD false).toNat : ℤ) := by
  cases xs with
  | nil => simp [ofBits]
  | cons b t => simp only [ofBits_cons, List.tail_cons, List.headD_cons, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]; ring

/-! ## The leaf and the decision tree -/

/-- One branch of the tree: `asw_leaf` emits the bit `owOut` on `out` and sets the register
`rbw` to the borrow `owBw`, without touching anything else. -/
theorem asw_leaf_ev {main : Cmd} {owOut owBw : Bool} {rT rbw : Reg} {out : Stk}
    {E : List Bool} {C : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ho : X out = (E.map Glyph.bit).reverse ++ C) :
    ∃ s' n, Ev main (asw_leaf owOut owBw rT rbw out) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk out = ((E ++ [owOut]).map Glyph.bit).reverse ++ C ∧
      s'.reg rbw = Glyph.bit owBw ∧
      (∀ r : Reg, r ≠ rT → r ≠ rbw → s'.reg r = g r) ∧
      (∀ k : Stk, k ≠ out → s'.stk k = X k) := by
  let g1 : Reg → Glyph := Function.update g rT (Glyph.bit owOut)
  let X1 : Stk → List Glyph := Function.update X out (Glyph.bit owOut :: X out)
  let g2 : Reg → Glyph := Function.update g1 rbw (Glyph.bit owBw)
  have h1 : Ev main (.set rT (Glyph.bit owOut)) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_set' main rT _ g X
  have h2 : Ev main (.push out rT) ⟨g1, X⟩ ⟨g1, X1⟩ 1 := by
    simpa only [X1, g1, upReg_same] using ev_push' main out rT g1 X
  have h3 : Ev main (.set rbw (Glyph.bit owBw)) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 :=
    ev_set' main rbw _ g1 X1
  have hmain : Ev main (asw_leaf owOut owBw rT rbw out) ⟨g, X⟩ ⟨g2, X1⟩ 3 := by
    simp only [asw_leaf, seqs]
    exact Ev.seq h1 (Ev.seq h2 h3)
  refine ⟨⟨g2, X1⟩, 3, hmain, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp only [X1, upStk_same, ho, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
      List.singleton_append, List.append_assoc, List.cons_append]
  · exact upReg_same rbw
  · intro r hrT hrbw
    simp only [g2, g1]
    rw [upReg_ne hrbw, upReg_ne hrT]
  · intro k hk
    simpa only [X1] using upStk_ne hk

/-- The 3-level tree `asw_subTree`: emits `asw_subOutBit x y c` on `out` and leaves
`asw_subBw x y c` in `rbw`, where `x`, `y` are the bits held by `rX`, `rY` and `c` the digit
held by `rbw`.  Cost `6`; no other register or stack is touched. -/
theorem asw_subTree_ev {main : Cmd} {rX rY rbw rT : Reg} {out : Stk} {x y c : Bool}
    {E : List Bool} {C : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hx : g rX = Glyph.bit x) (hy : g rY = Glyph.bit y) (hc : g rbw = Glyph.bit c)
    (ho : X out = (E.map Glyph.bit).reverse ++ C) :
    ∃ s' n, Ev main (asw_subTree rX rY rbw rT out) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk out = ((E ++ [asw_subOutBit x y c]).map Glyph.bit).reverse ++ C ∧
      s'.reg rbw = Glyph.bit (asw_subBw x y c) ∧
      (∀ r : Reg, r ≠ rT → r ≠ rbw → s'.reg r = g r) ∧
      (∀ k : Stk, k ≠ out → s'.stk k = X k) := by
  rcases x <;> rcases y <;> rcases c
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit false false false)
        (owBw := asw_subBw false false false) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit false false true)
        (owBw := asw_subBw false false true) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit false true false)
        (owBw := asw_subBw false true false) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit false true true)
        (owBw := asw_subBw false true true) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit true false false)
        (owBw := asw_subBw true false false) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit true false true)
        (owBw := asw_subBw true false true) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit true true false)
        (owBw := asw_subBw true true false) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf
  · obtain ⟨s', n, hleaf, hn, hout, hreg, hframe, hstk⟩ :=
      asw_leaf_ev (owOut := asw_subOutBit true true true)
        (owBw := asw_subBw true true true) (main := main) (rT := rT) (rbw := rbw)
        (out := out) (g := g) (X := X) ho
    refine ⟨s', n + 3, ?_, by omega, hout, hreg, hframe, hstk⟩
    simp only [asw_subTree]
    (first | refine Ev.iteF (by rw [reg_mk, hx]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hx]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hy]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hy]) ?_)
    (first | refine Ev.iteF (by rw [reg_mk, hc]; decide) ?_ | refine Ev.iteT (by rw [reg_mk, hc]) ?_)
    exact hleaf


/-- Read one operand digit: `peek` the top of the marked region on `k` into `rU`; if it is the
marker the register `rX` is set to `false` and the marker is kept, otherwise the glyph (a bit)
is popped into `rX`.  Cost `3`. -/
theorem asw_read_ev {main : Cmd} {k : Stk} {rU rX : Reg} (hUX : rU ≠ rX)
    {ra : List Bool} {A : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X k = ra.map Glyph.bit ++ gmk k :: A) :
    ∃ s' n, Ev main (seqs [.peek k rU, .ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)])
        ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk k = ra.tail.map Glyph.bit ++ gmk k :: A ∧
      s'.reg rX = Glyph.bit (ra.headD false) ∧
      s'.reg rU = (ra.map Glyph.bit ++ gmk k :: A).headD Glyph.eos ∧
      (∀ r : Reg, r ≠ rU → r ≠ rX → s'.reg r = g r) ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  let g1 : Reg → Glyph := Function.update g rU ((X k).headD Glyph.eos)
  have h1 : Ev main (.peek k rU) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_peek' main k rU g X
  have hhead : g1 rU = (ra.map Glyph.bit ++ gmk k :: A).headD Glyph.eos := by
    simp only [g1, upReg_same, ha]
  rcases ra with _ | ⟨hx, ra'⟩
  · have hT : g1 rU = gmk k := by simpa using hhead
    let g2 : Reg → Glyph := Function.update g1 rX (Glyph.bit false)
    have hset : Ev main (.set rX (Glyph.bit false)) ⟨g1, X⟩ ⟨g2, X⟩ 1 :=
      ev_set' main rX _ g1 X
    have h2 : Ev main (.ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)) ⟨g1, X⟩ ⟨g2, X⟩ 2 :=
      Ev.iteT hT hset
    have hmain : Ev main (seqs [.peek k rU, .ite rU (gmk k) (.set rX (.bit false))
        (.pop k rX)]) ⟨g, X⟩ ⟨g2, X⟩ 3 := by
      simp only [seqs]
      exact Ev.seq h1 h2
    refine ⟨⟨g2, X⟩, 3, hmain, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ha
    · exact upReg_same rX
    · simp only [g2, upReg_ne hUX]
      exact hT
    · intro r hrU hrX
      simp only [g2, g1, upReg_ne hrX, upReg_ne hrU]
    · intro j hj; rfl
  · have hT : g1 rU ≠ gmk k := by
      rw [hhead]
      simp only [List.map_cons, List.headD_cons]
      exact fun h => by cases h
    let g2 : Reg → Glyph := Function.update g1 rX ((X k).headD Glyph.eos)
    let X2 : Stk → List Glyph := Function.update X k (X k).tail
    have hpop : Ev main (.pop k rX) ⟨g1, X⟩ ⟨g2, X2⟩ 1 := ev_pop' main k rX g1 X
    have h2 : Ev main (.ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)) ⟨g1, X⟩ ⟨g2, X2⟩ 2 :=
      Ev.iteF hT hpop
    have hmain : Ev main (seqs [.peek k rU, .ite rU (gmk k) (.set rX (.bit false))
        (.pop k rX)]) ⟨g, X⟩ ⟨g2, X2⟩ 3 := by
      simp only [seqs]
      exact Ev.seq h1 h2
    refine ⟨⟨g2, X2⟩, 3, hmain, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [X2, ha]
    · simp [g2, ha]
    · simp only [g2, upReg_ne hUX, hhead, List.map_cons, List.headD_cons]
    · intro r hrU hrX
      simp only [g2, g1, upReg_ne hrX, upReg_ne hrU]
    · intro j hj
      simp only [X2, upStk_ne hj]

/-- The conditional step of `asw_read_ev`: if the register `rU` holds the head of the marked
region on `k`, either set `rX` to `false` (marker on top, marker kept) or pop the bit into `rX`.
Cost `2`; only `rX` and stack `k` are affected. -/
theorem asw_readStep_ev {main : Cmd} {k : Stk} {rU rX : Reg}
    {ra : List Bool} {A : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X k = ra.map Glyph.bit ++ gmk k :: A)
    (hu : g rU = (ra.map Glyph.bit ++ gmk k :: A).headD Glyph.eos) :
    ∃ s' n, Ev main (.ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧
      s'.stk k = ra.tail.map Glyph.bit ++ gmk k :: A ∧
      s'.reg rX = Glyph.bit (ra.headD false) ∧
      (∀ r : Reg, r ≠ rX → s'.reg r = g r) ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  rcases ra with _ | ⟨hx, ra'⟩
  · have hT : g rU = gmk k := by simpa using hu
    let g2 : Reg → Glyph := Function.update g rX (Glyph.bit false)
    have hset : Ev main (.set rX (Glyph.bit false)) ⟨g, X⟩ ⟨g2, X⟩ 1 := ev_set' main rX _ g X
    have h2 : Ev main (.ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)) ⟨g, X⟩ ⟨g2, X⟩ 2 :=
      Ev.iteT hT hset
    refine ⟨⟨g2, X⟩, 2, h2, le_rfl, ?_, ?_, ?_, ?_⟩
    · simpa using ha
    · exact upReg_same rX
    · intro r hrX; simp only [g2, upReg_ne hrX]
    · intro j hj; rfl
  · have hT : g rU ≠ gmk k := by
      rw [hu]
      simp only [List.map_cons, List.headD_cons]
      exact fun h => by cases h
    let g2 : Reg → Glyph := Function.update g rX ((X k).headD Glyph.eos)
    let X2 : Stk → List Glyph := Function.update X k (X k).tail
    have hpop : Ev main (.pop k rX) ⟨g, X⟩ ⟨g2, X2⟩ 1 := ev_pop' main k rX g X
    have h2 : Ev main (.ite rU (gmk k) (.set rX (.bit false)) (.pop k rX)) ⟨g, X⟩ ⟨g2, X2⟩ 2 :=
      Ev.iteF hT hpop
    refine ⟨⟨g2, X2⟩, 2, h2, le_rfl, ?_, ?_, ?_, ?_⟩
    · simp [X2, ha]
    · simp [g2, ha]
    · intro r hrX; simp only [g2, upReg_ne hrX]
    · intro j hj; simp only [X2, upStk_ne hj]

/-! ## Arithmetic steps for the loop invariant -/

/-- The step of the `ofBits` invariant for one consumed digit. -/
theorem asw_sub_cons_step (ra rb : List Bool) (c : Bool) (e1 : List Bool) (bw1 : Bool)
    (h : (ofBits e1 : ℤ) = (ofBits ra.tail : ℤ) - (ofBits rb.tail : ℤ)
        + 2 ^ e1.length * (bw1.toNat : ℤ) - ((asw_subBw (ra.headD false) (rb.headD false) c).toNat : ℤ)) :
    (ofBits (asw_subOutBit (ra.headD false) (rb.headD false) c :: e1) : ℤ)
      = (ofBits ra : ℤ) - (ofBits rb : ℤ)
        + 2 ^ (asw_subOutBit (ra.headD false) (rb.headD false) c :: e1).length * (bw1.toNat : ℤ)
        - (c.toNat : ℤ) := by
  have hk := asw_sub_digit_key (ra.headD false) (rb.headD false) c
  have hA := ofBits_head ra
  have hB := ofBits_head rb
  rw [ofBits_cons]
  push_cast
  rw [h, List.length_cons, pow_succ]
  push_cast
  ring_nf
  linarith [hk, hA, hB]

/-- The final digit emitted when both operands are exhausted. -/
theorem asw_sub_zero_step (c : Bool) :
    (ofBits [asw_subOutBit false false c] : ℤ)
      = (ofBits ([] : List Bool) : ℤ) - (ofBits ([] : List Bool) : ℤ)
        + 2 ^ ([asw_subOutBit false false c] : List Bool).length
            * ((asw_subBw false false c).toNat : ℤ)
        - (c.toNat : ℤ) := by
  have hk := asw_sub_digit_key false false c
  simp only [ofBits, List.foldr_nil, List.foldr_cons, List.length_cons, List.length_nil,
    pow_one, mul_zero, add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
    Bool.toNat_false] at *
  push_cast
  linarith

/-! ## The loop stop test -/

/-- The final flag test of the loop: after `set rF gGo`, if both marked regions on `a` and `b`
are exhausted the flag becomes `gStop` (via a `set`), otherwise it stays `gGo` (all branches
with `skip`).  Cost `≤ 4`; no stack is touched and `rC`, `rD` keep their values. -/
theorem asw_stop_test {main : Cmd} {a b : Stk} {ra rb : List Bool} {A B : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hu : g rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos)
    (hv : g rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos)
    (hF : g rF = gGo) :
    ∃ s' n, Ev main (seqs [.set rF gGo,
        .ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip]) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk = X ∧ s'.reg rC = g rC ∧ s'.reg rD = g rD ∧
      s'.reg rF = (if ra = [] ∧ rb = [] then gStop else gGo) := by
  let g5 : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g5, X⟩ 1 := ev_set' main rF gGo g X
  have hU : g5 rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    simp only [g5, upReg_ne (show rU ≠ rF by decide)]
    exact hu
  have hV : g5 rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    simp only [g5, upReg_ne (show rV ≠ rF by decide)]
    exact hv
  rcases ra with _ | ⟨hx, ra'⟩
  · rcases rb with _ | ⟨hy, rb'⟩
    · have hT1 : g5 rU = gmk a := by simpa using hU
      have hT2 : g5 rV = gmk b := by simpa using hV
      have h2 : Ev main (.ite rV (gmk b) (.set rF gStop) .skip) ⟨g5, X⟩
          ⟨Function.update g5 rF gStop, X⟩ 2 :=
        Ev.iteT hT2 (ev_set' main rF gStop g5 X)
      have h3 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
          ⟨g5, X⟩ ⟨Function.update g5 rF gStop, X⟩ 3 := Ev.iteT hT1 h2
      have hmain : Ev main (seqs [.set rF gGo, .ite rU (gmk a)
          (.ite rV (gmk b) (.set rF gStop) .skip) .skip]) ⟨g, X⟩
          ⟨Function.update g5 rF gStop, X⟩ 4 := by
        simp only [seqs]
        exact Ev.seq hset h3
      refine ⟨⟨Function.update g5 rF gStop, X⟩, 4, hmain, le_rfl, rfl, ?_, ?_, ?_⟩
      · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
      · simp only [g5, upReg_ne (show rD ≠ rF by decide)]
      · simp [g5, upReg_same]
    · have hT1 : g5 rU = gmk a := by simpa using hU
      have hT2 : g5 rV ≠ gmk b := by
        rw [hV]
        simp only [List.map_cons, List.headD_cons]
        exact fun h => by cases h
      have h2 : Ev main (.ite rV (gmk b) (.set rF gStop) .skip) ⟨g5, X⟩ ⟨g5, X⟩ 2 :=
        Ev.iteF hT2 (ev_skip main ⟨g5, X⟩)
      have h3 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
          ⟨g5, X⟩ ⟨g5, X⟩ 3 := Ev.iteT hT1 h2
      have hmain : Ev main (seqs [.set rF gGo, .ite rU (gmk a)
          (.ite rV (gmk b) (.set rF gStop) .skip) .skip]) ⟨g, X⟩ ⟨g5, X⟩ 4 := by
        simp only [seqs]
        exact Ev.seq hset h3
      refine ⟨⟨g5, X⟩, 4, hmain, le_rfl, rfl, ?_, ?_, ?_⟩
      · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
      · simp only [g5, upReg_ne (show rD ≠ rF by decide)]
      · simp [g5, upReg_same]
  · have hT1 : g5 rU ≠ gmk a := by
      rw [hU]
      simp only [List.map_cons, List.headD_cons]
      exact fun h => by cases h
    have h2 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
        ⟨g5, X⟩ ⟨g5, X⟩ 2 := Ev.iteF hT1 (ev_skip main ⟨g5, X⟩)
    have hmain : Ev main (seqs [.set rF gGo, .ite rU (gmk a)
        (.ite rV (gmk b) (.set rF gStop) .skip) .skip]) ⟨g, X⟩ ⟨g5, X⟩ 3 := by
      simp only [seqs]
      exact Ev.seq hset h2
    refine ⟨⟨g5, X⟩, 3, hmain, by omega, rfl, ?_, ?_, ?_⟩
    · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
    · simp only [g5, upReg_ne (show rD ≠ rF by decide)]
    · simp [g5, upReg_same]

/-! ## One iteration of the loop -/

/-- One iteration of the subtractor: read one digit of each operand (a `false` digit when the
region is exhausted), emit the two's complement digits of `x - y - c` on `o1` and of `y - x - d`
on `o2` (updating the borrows in `rC`, `rD`), and set the loop flag to `gStop` exactly when both
regions are exhausted.  Cost `≤ 22`. -/
theorem asw_subBody_ev {main : Cmd} {a b o1 o2 : Stk} (hab : a ≠ b) (ha1 : a ≠ o1)
    (ha2 : a ≠ o2) (hb1 : b ≠ o1) (hb2 : b ≠ o2) (ho : o1 ≠ o2)
    {ra rb : List Bool} {A B C1 C2 : List Glyph} {c d : Bool}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hF : g rF = gGo) (hC : g rC = Glyph.bit c) (hD : g rD = Glyph.bit d)
    (ha : X a = ra.map Glyph.bit ++ gmk a :: A)
    (hb : X b = rb.map Glyph.bit ++ gmk b :: B)
    (ho1 : X o1 = C1) (ho2 : X o2 = C2) :
    ∃ s' n, Ev main (asw_subBody a b o1 o2 rC rD rT rX rY rU rV rF) ⟨g, X⟩ s' n ∧ n ≤ 22 ∧
      s'.stk a = ra.tail.map Glyph.bit ++ gmk a :: A ∧
      s'.stk b = rb.tail.map Glyph.bit ++ gmk b :: B ∧
      s'.stk o1 = ([asw_subOutBit (ra.headD false) (rb.headD false) c].map Glyph.bit).reverse ++ C1 ∧
      s'.stk o2 = ([asw_subOutBit (rb.headD false) (ra.headD false) d].map Glyph.bit).reverse ++ C2 ∧
      s'.reg rC = Glyph.bit (asw_subBw (ra.headD false) (rb.headD false) c) ∧
      s'.reg rD = Glyph.bit (asw_subBw (rb.headD false) (ra.headD false) d) ∧
      s'.reg rF = (if ra = [] ∧ rb = [] then gStop else gGo) := by
  let g1 : Reg → Glyph := Function.update g rU ((X a).headD Glyph.eos)
  have hpeekA : Ev main (.peek a rU) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_peek' main a rU g X
  have hu1 : g1 rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    simp only [g1, upReg_same, ha]
  obtain ⟨s1, n1, hiteA, hn1, h1a, h1X, hf1, hs1⟩ :=
    asw_readStep_ev (main := main) (k := a) (rU := rU) (rX := rX) ha hu1
  have kbs1 : s1.stk b = rb.map Glyph.bit ++ gmk b :: B := by rw [hs1 b hab.symm]; exact hb
  let g3 : Reg → Glyph := Function.update s1.reg rV ((s1.stk b).headD Glyph.eos)
  have hpeekB : Ev main (.peek b rV) s1 ⟨g3, s1.stk⟩ 1 := ev_peek' main b rV s1.reg s1.stk
  have hu3 : g3 rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    simp only [g3, upReg_same, kbs1]
  obtain ⟨s2, n2, hiteB, hn2, h2b, h2Y, hf2, hs2⟩ :=
    asw_readStep_ev (main := main) (k := b) (rU := rV) (rX := rY) kbs1 hu3
  have kA2 : s2.stk a = ra.tail.map Glyph.bit ++ gmk a :: A := by rw [hs2 a hab]; exact h1a
  have kX2 : s2.reg rX = Glyph.bit (ra.headD false) := by rw [hf2 rX (by decide)]; exact h1X
  have kY2 : s2.reg rY = Glyph.bit (rb.headD false) := h2Y
  have kC2 : s2.reg rC = Glyph.bit c := by
    rw [hf2 rC (by decide)]
    simp only [g3, upReg_ne (show rC ≠ rV by decide)]
    rw [hf1 rC (by decide)]
    exact hC
  have kD2 : s2.reg rD = Glyph.bit d := by
    rw [hf2 rD (by decide)]
    simp only [g3, upReg_ne (show rD ≠ rV by decide)]
    rw [hf1 rD (by decide)]
    exact hD
  have kF2 : s2.reg rF = gGo := by
    rw [hf2 rF (by decide)]
    simp only [g3, upReg_ne (show rF ≠ rV by decide)]
    rw [hf1 rF (by decide)]
    exact hF
  have kU2 : s2.reg rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    rw [hf2 rU (by decide)]
    simp only [g3, upReg_ne (show rU ≠ rV by decide)]
    rw [hf1 rU (by decide)]
    exact hu1
  have kV2 : s2.reg rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    rw [hf2 rV (by decide)]
    exact hu3
  have kO1 : s2.stk o1 = C1 := by rw [hs2 o1 hb1.symm, hs1 o1 ha1.symm]; exact ho1
  have kO2 : s2.stk o2 = C2 := by rw [hs2 o2 hb2.symm, hs1 o2 ha2.symm]; exact ho2
  obtain ⟨s3, n3, ht1, hn3, h3o1, h3C, hf3, hs3⟩ :=
    asw_subTree_ev (main := main) (rX := rX) (rY := rY) (rbw := rC) (rT := rT) (out := o1)
      (g := s2.reg) (X := s2.stk) (E := []) (C := C1) kX2 kY2 kC2 (by simpa using kO1)
  obtain ⟨s4, n4, ht2, hn4, h4o2, h4D, hf4, hs4⟩ :=
    asw_subTree_ev (main := main) (rX := rY) (rY := rX) (rbw := rD) (rT := rT) (out := o2)
      (g := s3.reg) (X := s3.stk) (E := []) (C := C2)
      (by rw [hf3 rY (by decide) (by decide)]; exact kY2)
      (by rw [hf3 rX (by decide) (by decide)]; exact kX2)
      (by rw [hf3 rD (by decide) (by decide)]; exact kD2)
      (by rw [hs3 o2 ho.symm]; exact kO2)
  have kA4 : s4.stk a = ra.tail.map Glyph.bit ++ gmk a :: A := by
    rw [hs4 a ha2, hs3 a ha1]; exact kA2
  have kB4 : s4.stk b = rb.tail.map Glyph.bit ++ gmk b :: B := by
    rw [hs4 b hb2, hs3 b hb1]; exact h2b
  have kU4 : s4.reg rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    rw [hf4 rU (by decide) (by decide), hf3 rU (by decide) (by decide)]; exact kU2
  have kV4 : s4.reg rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    rw [hf4 rV (by decide) (by decide), hf3 rV (by decide) (by decide)]; exact kV2
  have kF4 : s4.reg rF = gGo := by
    rw [hf4 rF (by decide) (by decide), hf3 rF (by decide) (by decide)]; exact kF2
  have kC4 : s4.reg rC = Glyph.bit (asw_subBw (ra.headD false) (rb.headD false) c) := by
    rw [hf4 rC (by decide) (by decide)]; exact h3C
  have kO14 : s4.stk o1 =
      ([asw_subOutBit (ra.headD false) (rb.headD false) c].map Glyph.bit).reverse ++ C1 :=
    (hs4 o1 ho).trans (by simpa only [List.nil_append] using h3o1)
  obtain ⟨s5, n5, hstop, hn5, h5stk, h5C, h5D, h5F⟩ :=
    asw_stop_test (main := main) (a := a) (b := b) (ra := ra) (rb := rb)
      (A := A) (B := B) (g := s4.reg) (X := s4.stk) kU4 kV4 kF4
  have hbody : Ev main (asw_subBody a b o1 o2 rC rD rT rX rY rU rV rF) ⟨g, X⟩ s5
      (1 + (n1 + (1 + (n2 + (n3 + (n4 + n5)))))) := by
    simp only [asw_subBody, seqs]
    exact Ev.seq hpeekA (Ev.seq hiteA (Ev.seq hpeekB (Ev.seq hiteB
      (Ev.seq ht1 (Ev.seq ht2 hstop)))))
  refine ⟨s5, _, hbody, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5stk]; exact kA4
  · rw [h5stk]; exact kB4
  · rw [h5stk]; exact kO14
  · rw [h5stk]; exact h4o2
  · rw [h5C]; exact kC4
  · rw [h5D]; exact h4D
  · exact h5F

/-! ## The loop -/

/-- The subtractor loop: starting with borrows `c`, `d` in `rC`, `rD` and the flag `gGo` in `rF`,
it consumes both marked regions and emits the two's complement digits of `ra - rb` and of
`rb - ra`.  The trailing `- c.toNat`, `- d.toNat` in the arithmetic account for the incoming
borrows.  Induction on `ra.length + rb.length` (each iteration consumes at least one digit). -/
theorem asw_subLoop_loop_ev {main : Cmd} {a b o1 o2 : Stk} (hab : a ≠ b) (ha1 : a ≠ o1)
    (ha2 : a ≠ o2) (hb1 : b ≠ o1) (hb2 : b ≠ o2) (ho : o1 ≠ o2) :
    ∀ (m : ℕ) (ra rb : List Bool), ra.length + rb.length ≤ m →
      ∀ (c d : Bool) (A B C1 C2 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
        g rF = gGo → g rC = Glyph.bit c → g rD = Glyph.bit d →
        X a = ra.map Glyph.bit ++ gmk a :: A → X b = rb.map Glyph.bit ++ gmk b :: B →
        X o1 = C1 → X o2 = C2 →
        ∃ s' n, Ev main (.loop rF gGo (asw_subBody a b o1 o2 rC rD rT rX rY rU rV rF)) ⟨g, X⟩ s' n ∧
          n ≤ 25 * (ra.length + rb.length + 2) ∧
          s'.stk a = gmk a :: A ∧ s'.stk b = gmk b :: B ∧
          ∃ (e1 e2 : List Bool) (bw1 bw2 : Bool),
            s'.stk o1 = (e1.map Glyph.bit).reverse ++ C1 ∧
            s'.stk o2 = (e2.map Glyph.bit).reverse ++ C2 ∧
            s'.reg rC = Glyph.bit bw1 ∧ s'.reg rD = Glyph.bit bw2 ∧
            (ofBits e1 : ℤ) = (ofBits ra : ℤ) - (ofBits rb : ℤ)
              + 2 ^ e1.length * (bw1.toNat : ℤ) - (c.toNat : ℤ) ∧
            (ofBits e2 : ℤ) = (ofBits rb : ℤ) - (ofBits ra : ℤ)
              + 2 ^ e2.length * (bw2.toNat : ℤ) - (d.toNat : ℤ) := by
  intro m
  induction m with
  | zero =>
      intro ra rb hlen c d A B C1 C2 g X hF hC hD ha hb ho1 ho2
      have hra : ra = [] := List.length_eq_zero_iff.mp (by omega)
      have hrb : rb = [] := List.length_eq_zero_iff.mp (by omega)
      subst hra
      subst hrb
      obtain ⟨s1, n1, hbody, hn1, h1a, h1b, h1o1, h1o2, h1C, h1D, h1F⟩ :=
        asw_subBody_ev (main := main) hab ha1 ha2 hb1 hb2 ho hF hC hD ha hb ho1 ho2
      have h1F' : s1.reg rF = gStop := by rw [h1F]; simp
      have hne : s1.reg rF ≠ gGo := by rw [h1F']; decide
      refine ⟨s1, n1 + 1 + 1, Ev.loopT hF hbody (Ev.loopF hne), by omega, ?_, ?_, ?_⟩
      · simpa using h1a
      · simpa using h1b
      · refine ⟨[asw_subOutBit false false c], [asw_subOutBit false false d],
          asw_subBw false false c, asw_subBw false false d, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using h1o1
        · simpa using h1o2
        · simpa using h1C
        · simpa using h1D
        · simpa using asw_sub_zero_step c
        · simpa using asw_sub_zero_step d
  | succ m ih =>
      intro ra rb hlen c d A B C1 C2 g X hF hC hD ha hb ho1 ho2
      obtain ⟨s1, n1, hbody, hn1, h1a, h1b, h1o1, h1o2, h1C, h1D, h1F⟩ :=
        asw_subBody_ev (main := main) hab ha1 ha2 hb1 hb2 ho hF hC hD ha hb ho1 ho2
      by_cases hstop : ra = [] ∧ rb = []
      · have h1F' : s1.reg rF = gStop := by rw [h1F]; simp [hstop]
        have hne : s1.reg rF ≠ gGo := by rw [h1F']; decide
        refine ⟨s1, n1 + 1 + 1, Ev.loopT hF hbody (Ev.loopF hne), by omega, ?_, ?_, ?_⟩
        · simpa [hstop.1] using h1a
        · simpa [hstop.2] using h1b
        · refine ⟨[asw_subOutBit false false c], [asw_subOutBit false false d],
            asw_subBw false false c, asw_subBw false false d, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [hstop.1, hstop.2] using h1o1
          · simpa [hstop.1, hstop.2] using h1o2
          · simpa [hstop.1, hstop.2] using h1C
          · simpa [hstop.1, hstop.2] using h1D
          · simpa [hstop.1, hstop.2] using asw_sub_zero_step c
          · simpa [hstop.1, hstop.2] using asw_sub_zero_step d
      · have htl : ra.tail.length + rb.tail.length + 1 ≤ ra.length + rb.length := by
          rcases ra with _ | ⟨hx, ra'⟩ <;> rcases rb with _ | ⟨hy, rb'⟩
          · exact absurd ⟨rfl, rfl⟩ hstop
          · simp only [List.length_nil, List.tail_nil, List.length_cons, List.tail_cons]
            omega
          · simp only [List.length_nil, List.tail_nil, List.length_cons, List.tail_cons]
            omega
          · simp only [List.length_cons, List.tail_cons]
            omega
        have hlen' : ra.tail.length + rb.tail.length ≤ m := by omega
        obtain ⟨s2, n2, hloop2, hn2, h2a, h2b, e1, e2, bw1, bw2, h2o1, h2o2, h2C, h2D, h2e1, h2e2⟩ :=
          ih ra.tail rb.tail hlen' (asw_subBw (ra.headD false) (rb.headD false) c)
            (asw_subBw (rb.headD false) (ra.headD false) d) A B (s1.stk o1) (s1.stk o2)
            s1.reg s1.stk (by rw [h1F]; simp [hstop]) h1C h1D h1a h1b rfl rfl
        refine ⟨s2, n1 + n2 + 1, Ev.loopT hF hbody hloop2, by omega, h2a, h2b, ?_⟩
        refine ⟨asw_subOutBit (ra.headD false) (rb.headD false) c :: e1,
          asw_subOutBit (rb.headD false) (ra.headD false) d :: e2, bw1, bw2,
          ?_, ?_, h2C, h2D, ?_, ?_⟩
        · rw [h2o1, h1o1]
          simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.append_assoc]
        · rw [h2o2, h1o2]
          simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.append_assoc]
        · exact asw_sub_cons_step ra rb c e1 bw1 h2e1
        · exact asw_sub_cons_step rb ra d e2 bw2 h2e2

theorem asw_subLoop_spec {main : HvdH.Cmd} (a b o1 o2 : HvdH.Stk) (hab : a ≠ b) (ha1 : a ≠ o1)
    (ha2 : a ≠ o2) (hb1 : b ≠ o1) (hb2 : b ≠ o2) (ho : o1 ≠ o2) :
    ∀ (ra rb : List Bool) (A B C1 C2 : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X a = ra.map HvdH.Glyph.bit ++ Work.IntLib.AddSub.gmk a :: A →
      X b = rb.map HvdH.Glyph.bit ++ Work.IntLib.AddSub.gmk b :: B →
      X o1 = C1 → X o2 = C2 →
      ∃ s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_subLoop a b o1 o2) ⟨g, X⟩ s' n ∧
        n ≤ 31 * (ra.length + rb.length + 2) ∧
        s'.stk a = Work.IntLib.AddSub.gmk a :: A ∧
        s'.stk b = Work.IntLib.AddSub.gmk b :: B ∧
        ∃ (e1 e2 : List Bool) (bw1 bw2 : Bool),
          s'.stk o1 = (e1.map HvdH.Glyph.bit).reverse ++ C1 ∧
          s'.stk o2 = (e2.map HvdH.Glyph.bit).reverse ++ C2 ∧
          s'.reg Work.IntLib.AddSub.rC = HvdH.Glyph.bit bw1 ∧
          s'.reg Work.IntLib.AddSub.rD = HvdH.Glyph.bit bw2 ∧
          (Work.IntLib.ofBits e1 : ℤ) = (Work.IntLib.ofBits ra : ℤ) - (Work.IntLib.ofBits rb : ℤ)
            + 2 ^ e1.length * bw1.toNat ∧
          (Work.IntLib.ofBits e2 : ℤ) = (Work.IntLib.ofBits rb : ℤ) - (Work.IntLib.ofBits ra : ℤ)
            + 2 ^ e2.length * bw2.toNat := by
  intro ra rb A B C1 C2 g X ha hb ho1 ho2
  let g1 : Reg → Glyph := Function.update g rF gGo
  let g2 : Reg → Glyph := Function.update g1 rC (Glyph.bit false)
  let g3 : Reg → Glyph := Function.update g2 rD (Glyph.bit false)
  have hs1 : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_set' main rF gGo g X
  have hs2 : Ev main (.set rC (Glyph.bit false)) ⟨g1, X⟩ ⟨g2, X⟩ 1 := ev_set' main rC _ g1 X
  have hs3 : Ev main (.set rD (Glyph.bit false)) ⟨g2, X⟩ ⟨g3, X⟩ 1 := ev_set' main rD _ g2 X
  have hF3 : g3 rF = gGo := by
    simp only [g3, g2, g1, upReg_ne (show rF ≠ rD by decide),
      upReg_ne (show rF ≠ rC by decide), upReg_same]
  have hC3 : g3 rC = Glyph.bit false := by
    simp only [g3, g2, g1, upReg_ne (show rC ≠ rD by decide), upReg_same]
  have hD3 : g3 rD = Glyph.bit false := by
    simp only [g3, g2, g1, upReg_same]
  obtain ⟨s4, n4, hloop, hn4, h4a, h4b, e1, e2, bw1, bw2, h4o1, h4o2, h4C, h4D, h4e1, h4e2⟩ :=
    asw_subLoop_loop_ev (main := main) hab ha1 ha2 hb1 hb2 ho (ra.length + rb.length) ra rb le_rfl
      false false A B C1 C2 g3 X hF3 hC3 hD3 ha hb ho1 ho2
  have hmain : Ev main (asw_subLoop a b o1 o2) ⟨g, X⟩ s4 (1 + (1 + (1 + n4))) := by
    simp only [asw_subLoop, seqs]
    exact Ev.seq hs1 (Ev.seq hs2 (Ev.seq hs3 hloop))
  refine ⟨s4, 1 + (1 + (1 + n4)), hmain, by omega, h4a, h4b,
    e1, e2, bw1, bw2, h4o1, h4o2, h4C, h4D, ?_, ?_⟩
  · simpa [Bool.toNat_false] using h4e1
  · simpa [Bool.toNat_false] using h4e2

end AddSub
end Work.IntLib
