import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.divPush
import Submission.Work.IntLib.rippleArith
import Submission.Work.IntLib.div_shiftR
import Submission.Work.IntLib.div_rippleMain
import Submission.Work.IntLib.Shift.Loop
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.eval_mvRev
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.eval_dropRgn
import Submission.Work.IntLib.eval_subBitProg
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.subRippleBits_padBits
import Submission.Work.IntLib.divFoldAPI

/-!
# IntLib division: the main loop of the long-division core

This file proves `Work.IntLib.div_mainLoop`, the specification of `Div.mainLoopProg`: running the
long-division loop on the dividend bits still pending on `stP` produces the quotient bits on `stQ`
and the remainder bits on `stR`, with `bv * qv' + rv' = bval A` and `rv' < bv`.

The proof has four layers:

* `Work.IntLib.shiftR_ev`: one shift of the remainder region (`Div.shiftR`), the list arithmetic
  (`padBits_shift`, `subRippleBits_dstep`) that turns the shifted window into `dstep`;
* the state family `mSt` of the main loop, indexed by the number of processed dividend bits;
* `mainWork_ev`/`mainStep_ev`: one iteration of the loop, built from `di_rippleMain` (the ripple
  subtraction) and the two conditional branches;
* the unrolling of the loop with `eval_loop_iterate_le`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.IntLib

open HvdH

/-! ## Pure list and arithmetic facts -/

theorem foldl_bval (C : List Bool) (n : ℕ) :
    C.foldl (fun acc b => 2 * acc + b.toNat) n = 2 ^ C.length * n + bval C := by
  induction C generalizing n with
  | nil => simp [bval]
  | cons b C ih =>
    rw [List.foldl_cons, ih]
    have hb : bval (b :: C) = 2 ^ C.length * b.toNat + bval C := by
      have h : 2 * 0 + b.toNat = b.toNat := by omega
      have h1 : bval (b :: C) = C.foldl (fun acc b => 2 * acc + b.toNat) b.toNat := by
        rw [bval, List.foldl_cons, h]
      rw [h1, ih]
    rw [hb, List.length_cons]
    ring

theorem bval_cons (b : Bool) (C : List Bool) :
    bval (b :: C) = 2 ^ C.length * b.toNat + bval C := by
  have h : 2 * 0 + b.toNat = b.toNat := by omega
  have h1 : bval (b :: C) = C.foldl (fun acc b => 2 * acc + b.toNat) b.toNat := by
    rw [bval, List.foldl_cons, h]
  rw [h1, foldl_bval]

theorem bval_append (B C : List Bool) : bval (B ++ C) = 2 ^ C.length * bval B + bval C := by
  induction B with
  | nil => simp [bval]
  | cons b B ih =>
    rw [List.cons_append, bval_cons, ih, bval_cons, List.length_append, pow_add]
    ring

theorem bval_take_drop (A : List Bool) (j : ℕ) (hj : j ≤ A.length) :
    bval A = 2 ^ (A.length - j) * bval (A.take j) + bval (A.drop j) := by
  have h : (A.drop j).length = A.length - j := List.length_drop
  calc bval A = bval (A.take j ++ A.drop j) := by rw [List.take_append_drop]
    _ = 2 ^ (A.drop j).length * bval (A.take j) + bval (A.drop j) := bval_append _ _
    _ = 2 ^ (A.length - j) * bval (A.take j) + bval (A.drop j) := by rw [h]

/-- The fold of the long-division step: starting from the state `(qv, rv)` and reading the bits of
`A` (most significant first), the value identity is `bv * q + r = 2^|A| * (bv * qv + rv) + bval A`. -/
theorem fold_dstep_val : ∀ (A : List Bool) (bv qv rv : ℕ),
    bv * (A.foldl (dstep bv) (qv, rv)).1 + (A.foldl (dstep bv) (qv, rv)).2 =
      2 ^ A.length * (bv * qv + rv) + bval A := by
  intro A
  induction A with
  | nil => intro bv qv rv; simp [bval]
  | cons b A ih =>
    intro bv qv rv
    rw [List.foldl_cons, ih, dstep_val, bval_cons, List.length_cons, pow_succ]
    ring

/-- The folded remainder stays below the divisor. -/
theorem fold_dstep_lt : ∀ (A : List Bool) (bv qv rv : ℕ), 0 < bv → rv < bv →
    (A.foldl (dstep bv) (qv, rv)).2 < bv := by
  intro A
  induction A with
  | nil => intro bv qv rv hbv hrv; simpa using hrv
  | cons b A ih =>
    intro bv qv rv hbv hrv
    rw [List.foldl_cons]
    exact ih bv (dstep bv (qv, rv) b).1 (dstep bv (qv, rv) b).2 hbv
      (dstep_snd_lt bv (qv, rv) b hbv hrv)

theorem bitsG_cons (b : Bool) (l : List Bool) :
    bitsG (b :: l) = Glyph.bit b :: bitsG l := rfl

/-- The shifted window of `L` bits of `2 * rv + d`: the new low bit followed by the old window
without its top bit. -/
theorem padBits_shift (rv bv : ℕ) (d : Bool) (L : ℕ) (hbv : 0 < bv) (hrv : rv < bv)
    (hL : L = bv.size + 1) :
    padBits (2 * rv + d.toNat) L = d :: (padBits rv L).take (L - 1) := by
  have hL1 : 1 ≤ L := by have := Nat.size_pos.mpr hbv; omega
  rw [padBits_bit d L rv hL1]
  have h : (padBits rv L).take (L - 1) = padBits rv (L - 1) := by
    rw [padBits, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
    rfl
  rw [h]

/-- The top bit of the `L`-bit window of `rv` is the padding zero when `rv < 2^(L-1)`. -/
theorem padBits_last_false (rv L : ℕ) (h : rv < 2 ^ (L - 1)) (hL1 : 1 ≤ L) :
    (padBits rv L).getLast? = some false := by
  rw [List.getLast?_eq_some_iff]
  refine ⟨padBits rv (L - 1), ?_⟩
  have h2 : rv < 2 ^ L := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine (ofBits_inj_of_length_eq _ _ ?_ ?_).symm
  · rw [padBits_length, List.length_append, padBits_length]; simp; omega
  · rw [ofBits_padBits, ofBits_append, ofBits_padBits, padBits_length rv (L - 1),
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h]
    simp [ofBits]

/-- The window of `L` bits of the shifted value stays below `2^L`. -/
theorem shiftWindow_lt (rv bv : ℕ) (d : Bool) (L : ℕ) (hbv : 0 < bv) (hrv : rv < bv)
    (hL : L = bv.size + 1) : 2 * rv + d.toNat < 2 ^ L := by
  have h1 : rv < 2 ^ (L - 1) := by
    have h : bv.size = L - 1 := by omega
    have h2 := Nat.lt_size_self bv
    rw [h] at h2
    omega
  have h2 : d.toNat ≤ 1 := by cases d <;> simp
  have h3 : 2 ^ L = 2 ^ (L - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  omega

/-- The ripple subtraction of `bv` from the shifted window `2 * rv + d` (of `L` bits). -/
theorem subRippleBits_dstep (rv bv : ℕ) (d : Bool) (L : ℕ) (hbv : 0 < bv) (hrv : rv < bv)
    (hL : L = bv.size + 1) :
    subRippleBits (padBits (2 * rv + d.toNat) L) (padBits bv L) false =
      (decide (bv > 2 * rv + d.toNat),
        padBits ((2 * rv + d.toNat + 2 ^ L - bv) % 2 ^ L) L) := by
  have hbv2 : bv < 2 ^ L := by
    have h : bv.size ≤ L := by omega
    exact lt_of_lt_of_le (Nat.lt_size_self bv) (Nat.pow_le_pow_right (by norm_num) h)
  exact subRippleBits_padBits _ _ _ (shiftWindow_lt rv bv d L hbv hrv hL) hbv2

/-- In the no-borrow case the ripple bits are the bits of `dstep`'s remainder. -/
theorem dstep_snd_eq (rv bv qv : ℕ) (d : Bool) (L : ℕ) (hX : 2 * rv + d.toNat < 2 ^ L)
    (h : bv ≤ 2 * rv + d.toNat) :
    padBits ((2 * rv + d.toNat + 2 ^ L - bv) % 2 ^ L) L = padBits (dstep bv (qv, rv) d).2 L := by
  have hsub : (dstep bv (qv, rv) d).2 = 2 * rv + d.toNat - bv := by
    have hd : (dstep bv (qv, rv) d).2
        = 2 * rv + d.toNat - (if bv ≤ 2 * rv + d.toNat then 1 else 0) * bv := rfl
    rw [hd, if_pos h, one_mul]
  rw [hsub]
  congr 1
  have h2 : 2 * rv + d.toNat - bv < 2 ^ L := by omega
  have h3 : 2 * rv + d.toNat + 2 ^ L - bv = (2 * rv + d.toNat - bv) + 2 ^ L := by omega
  have h4 : (2 * rv + d.toNat - bv) + 2 ^ L = (2 * rv + d.toNat - bv) + 1 * 2 ^ L := by ring
  rw [h3, h4, one_mul, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h2]

/-- In the borrow case `dstep`'s remainder is the shifted window itself. -/
theorem dstep_snd_borrow (rv bv qv : ℕ) (d : Bool) (h : 2 * rv + d.toNat < bv) :
    (dstep bv (qv, rv) d).2 = 2 * rv + d.toNat := by
  have hd : (dstep bv (qv, rv) d).2
      = 2 * rv + d.toNat - (if bv ≤ 2 * rv + d.toNat then 1 else 0) * bv := rfl
  rw [hd, if_neg (by omega), Nat.zero_mul, Nat.sub_zero]

/-! ## The state of the main loop

`lSt_dm S b0 p b r q` is the state of the long-division cache: the pending dividend bits `p` on `stP`,
the divisor bits `b` on `stB`, the remainder bits `r` on `stR` and the quotient bits `q` on `stQ`,
the three scratch stacks carrying only their markers, the nine stacks sitting above `b0`'s contents
and every other stack taken from `S`. -/

def lSt_dm (S b0 : State) (p b r q : List Bool) : State :=
  State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk
    (State.updStk (State.updStk (State.updStk S
      Div.stP (bitsG p ++ [gP] ++ b0.stk Div.stP))
      Div.stB (bitsG b ++ [gB] ++ b0.stk Div.stB))
      Div.stR (bitsG r ++ [gR] ++ b0.stk Div.stR))
      Div.stQ (bitsG q ++ [gQ] ++ b0.stk Div.stQ))
      Div.stS ([gS] ++ b0.stk Div.stS))
      Div.stC ([gC] ++ b0.stk Div.stC))
      Div.stD ([gD] ++ b0.stk Div.stD))
      Div.stX ([gX] ++ b0.stk Div.stX))
      Div.stY (b0.stk Div.stY)

macro "lSt_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [lSt_dm, State.updStk, State.updReg,
      Function.update_apply])

@[simp] theorem lSt_stkP (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stP = bitsG p ++ [gP] ++ b0.stk Div.stP := by lSt_simp
@[simp] theorem lSt_stkB (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stB = bitsG b ++ [gB] ++ b0.stk Div.stB := by lSt_simp
@[simp] theorem lSt_stkR (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stR = bitsG r ++ [gR] ++ b0.stk Div.stR := by lSt_simp
@[simp] theorem lSt_stkQ (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stQ = bitsG q ++ [gQ] ++ b0.stk Div.stQ := by lSt_simp
@[simp] theorem lSt_stkS (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stS = [gS] ++ b0.stk Div.stS := by lSt_simp
@[simp] theorem lSt_stkC (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stC = [gC] ++ b0.stk Div.stC := by lSt_simp
@[simp] theorem lSt_stkD (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stD = [gD] ++ b0.stk Div.stD := by lSt_simp
@[simp] theorem lSt_stkX (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stX = [gX] ++ b0.stk Div.stX := by lSt_simp
@[simp] theorem lSt_stkY (S b0 : State) (p b r q : List Bool) :
    (lSt_dm S b0 p b r q).stk Div.stY = b0.stk Div.stY := by lSt_simp
@[simp] theorem lSt_stk_ne (S b0 : State) (p b r q : List Bool) (j : Stk) (h1 : j ≠ Div.stP)
    (h2 : j ≠ Div.stB) (h3 : j ≠ Div.stR) (h4 : j ≠ Div.stQ) (h5 : j ≠ Div.stS)
    (h6 : j ≠ Div.stC) (h7 : j ≠ Div.stD) (h8 : j ≠ Div.stX) (h9 : j ≠ Div.stY) :
    (lSt_dm S b0 p b r q).stk j = S.stk j := by
  simp only [lSt_dm, State.updStk, Function.update_apply]
  rw [if_neg h9, if_neg h8, if_neg h7, if_neg h6, if_neg h5, if_neg h4, if_neg h3, if_neg h2,
    if_neg h1]
@[simp] theorem lSt_reg_dm (S b0 : State) (p b r q : List Bool) (r' : Reg) :
    (lSt_dm S b0 p b r q).reg r' = S.reg r' := rfl

/-- The state of the main loop at the beginning of the `i`-th iteration. -/
def mSt (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) : State :=
  (lSt_dm S b0 (A.drop i) (padBits bv L)
    (padBits ((A.take i).foldl (dstep bv) (qv, rv)).2 L)
    (padBits ((A.take i).foldl (dstep bv) (qv, rv)).1 (j + i))).updReg rLoop Glyph.eos

/-- The loop family: the state family `mSt` for the iterations, extended past the last one by the
terminal state (the marker of `stP` pushed back, the loop register set to `mk 0`). -/
def mFam (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) : State :=
  if i ≤ A.length then mSt S b0 A bv qv rv j L i
  else (mSt S b0 A bv qv rv j L A.length).updReg rLoop (Glyph.mk 0)

@[simp] theorem mFam_of_le (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ)
    (h : i ≤ A.length) : mFam S b0 A bv qv rv j L i = mSt S b0 A bv qv rv j L i := by
  simp [mFam, h]

@[simp] theorem mFam_of_gt (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ)
    (h : ¬ i ≤ A.length) :
    mFam S b0 A bv qv rv j L i = (mSt S b0 A bv qv rv j L A.length).updReg rLoop (Glyph.mk 0) := by
  simp [mFam, h]

@[simp] theorem mSt_stkP (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stP = bitsG (A.drop i) ++ [gP] ++ b0.stk Div.stP := by
  simp [mSt]
@[simp] theorem mSt_stkB (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB := by
  simp [mSt]
@[simp] theorem mSt_stkR (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stR =
      bitsG (padBits ((A.take i).foldl (dstep bv) (qv, rv)).2 L) ++ [gR] ++
        b0.stk Div.stR := by
  simp [mSt]
@[simp] theorem mSt_stkQ (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stQ =
      bitsG (padBits ((A.take i).foldl (dstep bv) (qv, rv)).1 (j + i)) ++ [gQ] ++
        b0.stk Div.stQ := by
  simp [mSt]
@[simp] theorem mSt_stkS (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stS = [gS] ++ b0.stk Div.stS := by simp [mSt]
@[simp] theorem mSt_stkC (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stC = [gC] ++ b0.stk Div.stC := by simp [mSt]
@[simp] theorem mSt_stkD (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stD = [gD] ++ b0.stk Div.stD := by simp [mSt]
@[simp] theorem mSt_stkX (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stX = [gX] ++ b0.stk Div.stX := by simp [mSt]
@[simp] theorem mSt_stkY (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).stk Div.stY = b0.stk Div.stY := by simp [mSt]
@[simp] theorem mSt_stk_ne (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) (k : Stk)
    (h1 : k ≠ Div.stP) (h2 : k ≠ Div.stB) (h3 : k ≠ Div.stR) (h4 : k ≠ Div.stQ)
    (h5 : k ≠ Div.stS) (h6 : k ≠ Div.stC) (h7 : k ≠ Div.stD) (h8 : k ≠ Div.stX)
    (h9 : k ≠ Div.stY) : (mSt S b0 A bv qv rv j L i).stk k = S.stk k :=
  lSt_stk_ne S b0 _ _ _ _ k h1 h2 h3 h4 h5 h6 h7 h8 h9
@[simp] theorem mSt_reg_rLoop (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) :
    (mSt S b0 A bv qv rv j L i).reg rLoop = Glyph.eos := by
  show ((lSt_dm S b0 (A.drop i) (padBits bv L) (padBits (A.foldl (dstep bv) (qv, rv)).2 L)
    (padBits (A.foldl (dstep bv) (qv, rv)).1 (j + i))).updReg rLoop Glyph.eos).reg rLoop
    = Glyph.eos
  rw [State.updReg_apply, if_pos rfl]
@[simp] theorem mSt_reg_ne (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) (r : Reg)
    (hr : r ≠ rLoop) : (mSt S b0 A bv qv rv j L i).reg r = S.reg r := by
  show ((lSt_dm S b0 (A.drop i) (padBits bv L) (padBits (A.foldl (dstep bv) (qv, rv)).2 L)
    (padBits (A.foldl (dstep bv) (qv, rv)).1 (j + i))).updReg rLoop Glyph.eos).reg r
    = S.reg r
  rw [State.updReg_apply, if_neg hr, lSt_reg_dm]

theorem bitsG_ne_mk (l : List Bool) (i : Fin 16) : ∀ g ∈ bitsG l, g ≠ Glyph.mk i := by
  intro g hg
  rw [bitsG, List.mem_map] at hg
  obtain ⟨b, _, rfl⟩ := hg
  exact fun h => nomatch h

/-! ## The shift step -/

theorem shiftR_ev (main : Cmd) (S b0 : State) (d : Bool) (rl : List Bool) (L : ℕ)
    (hL1 : 1 ≤ L) (hrl : rl.length = L)
    (hR : S.stk Div.stR = bitsG rl ++ [gR] ++ b0.stk Div.stR)
    (hX : S.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hrg : S.reg rLoop = Glyph.bit d) :
    ∃ s' n, Eval main Div.shiftR S s' n ∧ n ≤ 12 * (L + 1) + 40 ∧
      s'.stk Div.stR = bitsG (d :: rl.take (L - 1)) ++ [gR] ++ b0.stk Div.stR ∧
      s'.stk Div.stX = [gX] ++ b0.stk Div.stX ∧
      (∀ j, j ≠ Div.stR → j ≠ Div.stX → s'.stk j = S.stk j) := by
  have hne_RS : Div.stR ≠ Div.stX := by decide
  have hne_SR : Div.stX ≠ Div.stR := by decide
  let S1 : State := ⟨S.reg, Function.update S.stk Div.stR (S.reg rLoop :: S.stk Div.stR)⟩
  have e1 : Eval main (.push Div.stR rLoop) S S1 1 := Eval.push Div.stR rLoop S
  have hS1R : S1.stk Div.stR = bitsG (d :: rl) ++ gR :: b0.stk Div.stR := by
    show S.reg rLoop :: S.stk Div.stR = bitsG (d :: rl) ++ gR :: b0.stk Div.stR
    rw [hrg, hR]
    simp [bitsG]
  have hS1X : S1.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    show (Function.update S.stk Div.stR (S.reg rLoop :: S.stk Div.stR)) Div.stX = _
    rw [Function.update_of_ne hne_SR]; exact hX
  obtain ⟨S2, n2, e2, hn2, hS2R, hS2X, hfr2⟩ :=
    eval_mvRevOnto main Div.stR gR Div.stX Div.rgT (bitsG (d :: rl)) (b0.stk Div.stR)
      (S1.stk Div.stX) S1 (bitsG_ne_mk (d :: rl) 3) hS1R rfl hne_RS
  have hS2X' : S2.stk Div.stX = Glyph.bit (rl.getLast (by intro h; rw [h] at hrl; simp at hrl; omega))
      :: (bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d, gX] ++ b0.stk Div.stX) := by
    rw [hS2X, hS1X]
    rw [show bitsG (d :: rl) = Glyph.bit d :: bitsG rl from rfl, List.reverse_cons]
    rw [show (bitsG rl).reverse = bitsG rl.reverse from by rw [bitsG, ← List.map_reverse]]
    have hrlne : rl ≠ [] := by intro h; rw [h] at hrl; simp at hrl; omega
    have hrev : rl.reverse = rl.getLast hrlne :: rl.dropLast.reverse := by
      conv_lhs => rw [← List.dropLast_append_getLast hrlne]
      rw [List.reverse_append]; simp
    rw [hrev]
    rw [show rl.dropLast = rl.take (L - 1) from by rw [List.dropLast_eq_take, hrl]]
    simp
  let S3 : State := State.tPop S2 Div.stX Div.rgT
  have e3 : Eval main (.pop Div.stX Div.rgT) S2 S3 1 := Eval.pop _ _ _
  have hS3R : S3.stk Div.stR = b0.stk Div.stR := by
    show (Function.update S2.stk Div.stX (S2.stk Div.stX).tail) Div.stR = b0.stk Div.stR
    rw [Function.update_of_ne hne_RS]; exact hS2R
  have hS3X : S3.stk Div.stX = bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d, gX] ++ b0.stk Div.stX := by
    show (S2.stk Div.stX).tail = _
    rw [hS2X']; simp
  obtain ⟨S4, n4, e4, hn4, hS4X, hS4R, hfr4⟩ :=
    eval_mvRev main Div.stX gX Div.stR gR Div.rgT
      (bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d]) (b0.stk Div.stX) (b0.stk Div.stR) S3
      (by intro g hg
          rw [List.mem_append] at hg
          rcases hg with hg | hg
          · exact bitsG_ne_mk _ 8 g hg
          · simp at hg; subst hg; exact fun h => nomatch h)
      (by rw [hS3X]; simp) hS3R hne_SR
  have hrevl : (bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d]).reverse =
      bitsG (d :: rl.take (L - 1)) := by
    rw [List.reverse_append, List.reverse_singleton, bitsG, ← List.map_reverse,
      List.reverse_reverse, bitsG, List.map_cons]
    rfl
  have hS4R' : S4.stk Div.stR = bitsG (d :: rl.take (L - 1)) ++ [gR] ++ b0.stk Div.stR := by
    rw [hS4R, hrevl]
    simp
  let S5 : State := (S4.updReg Div.rgT gX).updStk Div.stX (gX :: S4.stk Div.stX)
  have e5 : Eval main (Div.mkG Div.stX gX) S4 S5 2 := Div.eval_mkG main Div.stX gX S4
  have hS5X : S5.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    show (Function.update S4.stk Div.stX (gX :: S4.stk Div.stX)) Div.stX = _
    rw [Function.update_self, hS4X]
    simp
  have hS5R : S5.stk Div.stR = bitsG (d :: rl.take (L - 1)) ++ [gR] ++ b0.stk Div.stR := by
    show (Function.update S4.stk Div.stX (gX :: S4.stk Div.stX)) Div.stR = _
    rw [Function.update_of_ne hne_RS]; exact hS4R'
  refine ⟨S5, 1 + (n2 + (1 + (n4 + (2 + 1)))), ?_, ?_, hS5R, hS5X, ?_⟩
  · have hshift : Div.shiftR = Div.seqs [.push Div.stR rLoop, mvRevOnto Div.stR gR Div.stX Div.rgT,
        .pop Div.stX Div.rgT, mvRev Div.stX gX Div.stR gR Div.rgT, Div.mkG Div.stX gX] := rfl
    rw [hshift]
    exact Div.eval_seqs_cons e1 (Div.eval_seqs_cons e2 (Div.eval_seqs_cons e3
      (Div.eval_seqs_cons e4 (Div.eval_seqs_cons e5 (Eval.skip _)))))
  · have hlen2 : (bitsG (d :: rl)).length = rl.length + 1 := by simp [bitsG]
    have hlen4 : (bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d]).length ≤ L := by
      have h4 : (bitsG (rl.take (L - 1)).reverse ++ [Glyph.bit d]).length
          = (rl.take (L - 1)).length + 1 := by simp [bitsG]
      have h5 : (rl.take (L - 1)).length ≤ L - 1 := List.length_take_le (L - 1) rl
      omega
    omega
  · intro j hjR hjX
    show (Function.update S4.stk Div.stX (gX :: S4.stk Div.stX)) j = S.stk j
    rw [Function.update_of_ne hjX]
    rw [hfr4 j hjX hjR]
    have h3 : S3.stk j = S2.stk j := by
      show (Function.update S2.stk Div.stX (S2.stk Div.stX).tail) j = S2.stk j
      rw [Function.update_of_ne hjX]
    rw [h3, hfr2 j hjR hjX]
    show (Function.update S.stk Div.stR (S.reg rLoop :: S.stk Div.stR)) j = S.stk j
    rw [Function.update_of_ne hjR]

/-- `Div.dropReg k T r` (a `consume` with the `skip` handler) drops the region of stack `k` above
its marker `T`, leaving the marker and everything below it. -/
theorem dropReg_ev (main : Cmd) (S : State) (k : Stk) (T : Glyph) (r : Reg) (l bl : List Glyph)
    (hT : ∀ g ∈ l, g ≠ T) (hk : S.stk k = l ++ [T] ++ bl) :
    ∃ s' n, Eval main (Div.dropReg k T r) S s' n ∧ n ≤ 5 * (l.length + 1) + 7 ∧
      s'.stk k = [T] ++ bl ∧ (∀ j, j ≠ k → s'.stk j = S.stk j) := by
  let Inv : List Glyph → State → Prop := fun gs t =>
    t.stk k = gs ++ T :: bl ∧ (∀ g ∈ gs, g ≠ T) ∧ (∀ j, j ≠ k → t.stk j = S.stk j)
  have hstk : ∀ gs t, Inv gs t → t.stk k = gs ++ T :: bl := fun gs t h => h.1
  have hterm : ∀ (g : Glyph) (gs : List Glyph) (t : State), Inv (g :: gs) t → g ≠ T := by
    intro g gs t h; exact h.2.1 g (by simp)
  have hreg : ∀ gs t (g : Glyph), Inv gs t → Inv gs ⟨Function.update t.reg r g, t.stk⟩ := by
    intro gs t g h; exact ⟨h.1, h.2.1, fun j hj => h.2.2 j hj⟩
  have hpop : ∀ (g : Glyph) (gs : List Glyph) (t : State), Inv (g :: gs) t →
      Inv gs ⟨Function.update t.reg r g, Function.update t.stk k (gs ++ T :: bl)⟩ := by
    intro g gs t h
    refine ⟨by simp, ?_, ?_⟩
    · intro x hx; exact h.2.1 x (List.mem_cons_of_mem g hx)
    · intro j hj
      show Function.update t.stk k (gs ++ T :: bl) j = S.stk j
      rw [Function.update_of_ne hj]
      exact h.2.2 j hj
  have hstep : ∀ (g : Glyph) (gs : List Glyph) (t : State), g ≠ T → t.reg r = g → Inv gs t →
      ∃ s' n, Eval main (Cmd.skip) t s' n ∧ n ≤ 1 ∧ Inv gs s' :=
    fun g gs t _ _ h => ⟨t, 1, Eval.skip t, le_refl 1, h⟩
  obtain ⟨s', n, hev, hinv, _, hn⟩ := consume_eval (main := main) (k := k) (T := T) (r := r)
    (handler := Cmd.skip) (Inv := Inv) (below := bl) (b := 1) hstk hterm hreg hpop hstep l S
    ⟨by rw [hk]; simp, hT, fun j _ => rfl⟩
  refine ⟨s', n, ?_, ?_, ?_, ?_⟩
  · simpa [Div.dropReg] using hev
  · omega
  · simpa using hinv.1
  · exact hinv.2.2

end Work.IntLib

namespace Work.IntLib

open HvdH

/-! ## The ripple subtraction of the main loop -/

theorem rippleMain_ev (main : Cmd) (b0 : State) (X Y : List Bool) (L : ℕ)
    (hX : X.length = L) (hY : Y.length = L) (S : State)
    (hR : S.stk Div.stR = bitsG X ++ [gR] ++ b0.stk Div.stR)
    (hB : S.stk Div.stB = bitsG Y ++ [gB] ++ b0.stk Div.stB)
    (hS5 : S.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : S.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : S.stk Div.stD = [gD] ++ b0.stk Div.stD) :
    ∃ s' n, Eval main Div.rippleMain S s' n ∧ n ≤ 15 * (L + 2) + 12 ∧
      s'.stk Div.stR = b0.stk Div.stR ∧
      s'.stk Div.stB = b0.stk Div.stB ∧
      s'.stk Div.stS = bitsG (subRippleBits X Y false).2.reverse ++ [gS] ++ b0.stk Div.stS ∧
      s'.stk Div.stC = bitsG Y.reverse ++ [gC] ++ b0.stk Div.stC ∧
      s'.stk Div.stD = bitsG X.reverse ++ [gD] ++ b0.stk Div.stD ∧
      s'.reg Div.rgC = Glyph.bit (subRippleBits X Y false).1 ∧
      (∀ j, j ≠ Div.stR → j ≠ Div.stB → j ≠ Div.stS → j ≠ Div.stC → j ≠ Div.stD →
        s'.stk j = S.stk j) :=
  div_rippleMain main b0 X Y L hX hY S hR hB hS5 hS6 hS7

/-! ## One iteration of the main loop -/

/-- `mainWork`: from the state of the main loop with the current remainder `padBits rv L` and
quotient `padBits qv jl`, the shift, ripple subtraction, restore of the divisor and the two
conditional moves leave the remainder `padBits (dstep bv (qv,rv) d).2 L` and append the quotient bit
`(dstep bv (qv,rv) d).1` to the quotient. -/
theorem mainWork_ev (main : Cmd) (s b0 : State) (d : Bool) (bv rv qv jl L : ℕ)
    (hbv : 0 < bv) (hrv : rv < bv) (hL : L = bv.size + 1)
    (hB : s.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv jl) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : s.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : s.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : s.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hrl : s.reg rLoop = Glyph.bit d) :
    ∃ s' n, Eval main Div.mainWork s s' n ∧ n ≤ 150 * (L + 1) ∧
      s'.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++ b0.stk Div.stR ∧
      s'.stk Div.stQ = bitsG (padBits (dstep bv (qv, rv) d).1 (jl + 1)) ++ [gQ] ++ b0.stk Div.stQ ∧
      (∀ j, j ≠ Div.stR → j ≠ Div.stQ → s'.stk j = s.stk j) := by
  have hL1 : 1 ≤ L := by have := Nat.size_pos.mpr hbv; omega
  have hsub := subRippleBits_dstep rv bv d L hbv hrv hL
  have hshift := padBits_shift rv bv d L hbv hrv hL
  -- step 1: the shift
  obtain ⟨s1, n1, e1, hn1, h1R, h1X, h1fr⟩ :=
    shiftR_ev main s b0 d (padBits rv L) L hL1 (padBits_length rv L) hR hS8 hrl
  have h1R' : s1.stk Div.stR = bitsG (padBits (2 * rv + d.toNat) L) ++ [gR] ++ b0.stk Div.stR := by
    rw [h1R, ← hshift]
  -- step 2: the ripple subtraction
  obtain ⟨s2, n2, e2, hn2, h2R, h2B, h2S, h2C, h2D, h2c, h2fr⟩ :=
    rippleMain_ev main b0 (padBits (2 * rv + d.toNat) L) (padBits bv L) L
      (padBits_length _ L) (padBits_length bv L) s1 h1R'
      (by rw [h1fr Div.stB (by decide) (by decide)]; exact hB)
      (by rw [h1fr Div.stS (by decide) (by decide)]; exact hS5)
      (by rw [h1fr Div.stC (by decide) (by decide)]; exact hS6)
      (by rw [h1fr Div.stD (by decide) (by decide)]; exact hS7)
  have h2c' : s2.reg Div.rgC = Glyph.bit (decide (bv > 2 * rv + d.toNat)) := by
    rw [h2c, hsub]
  -- step 3: restore the divisor region on `stB`
  have hl3 : (bitsG (padBits bv L).reverse).reverse = bitsG (padBits bv L) := by
    rw [bitsG, List.map_reverse, List.reverse_reverse]
  obtain ⟨s3, n3, e3, hn3, h3C, h3B, h3fr⟩ :=
    eval_mvRev main Div.stC gC Div.stB gB Div.rgT (bitsG (padBits bv L).reverse)
      (b0.stk Div.stC) (b0.stk Div.stB) s2
      (by intro g hg; rw [bitsG, List.mem_map] at hg
          obtain ⟨b, _, rfl⟩ := hg; exact fun h => nomatch h)
      (by rw [h2C]; simp) h2B (by decide)
  have h3B' : s3.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB := by
    rw [h3B, hl3]
    simp
  -- step 4: restore the marker of `stC`
  let s4 : State := (s3.updReg Div.rgT gC).updStk Div.stC (gC :: s3.stk Div.stC)
  have e4 : Eval main (Div.mkG Div.stC gC) s3 s4 2 := Div.eval_mkG main Div.stC gC s3
  have h4C : s4.stk Div.stC = [gC] ++ b0.stk Div.stC := by
    show (Function.update s3.stk Div.stC (gC :: s3.stk Div.stC)) Div.stC = _
    rw [Function.update_self, h3C]
    simp
  have h4fr : ∀ j, j ≠ Div.stC → s4.stk j = s3.stk j := by
    intro j hj
    show (Function.update s3.stk Div.stC (gC :: s3.stk Div.stC)) j = s3.stk j
    rw [Function.update_of_ne hj]
  have h4c : s4.reg Div.rgC = Glyph.bit (decide (bv > 2 * rv + d.toNat)) := by
    rw [Shift.Eval_reg_frame e4 (by decide : Div.rgC ∉ Shift.cmdRegs (Div.mkG Div.stC gC)),
      Shift.Eval_reg_frame e3 (by decide : Div.rgC ∉
        Shift.cmdRegs (mvRev Div.stC gC Div.stB gB Div.rgT)), h2c']
  -- facts about `s4` that both branches need
  have h4R : s4.stk Div.stR = b0.stk Div.stR := by
    rw [h4fr Div.stR (by decide), h3fr Div.stR (by decide) (by decide)]
    exact h2R
  have h4S : s4.stk Div.stS = bitsG (subRippleBits (padBits (2 * rv + d.toNat) L)
      (padBits bv L) false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
    rw [h4fr Div.stS (by decide), h3fr Div.stS (by decide) (by decide), h2S]
  have h4D : s4.stk Div.stD = bitsG (padBits (2 * rv + d.toNat) L).reverse ++ [gD] ++
      b0.stk Div.stD := by
    rw [h4fr Div.stD (by decide), h3fr Div.stD (by decide) (by decide), h2D]
  have h4Q : s4.stk Div.stQ = bitsG (padBits qv jl) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [h4fr Div.stQ (by decide), h3fr Div.stQ (by decide) (by decide),
      h2fr Div.stQ (by decide) (by decide) (by decide) (by decide) (by decide),
      h1fr Div.stQ (by decide) (by decide)]
    exact hQ
  have h4X : s4.stk Div.stX = s.stk Div.stX := by
    rw [h4fr Div.stX (by decide), h3fr Div.stX (by decide) (by decide),
      h2fr Div.stX (by decide) (by decide) (by decide) (by decide) (by decide),
      h1X, hS8]
  have h4P : s4.stk Div.stP = s.stk Div.stP := by
    rw [h4fr Div.stP (by decide), h3fr Div.stP (by decide) (by decide),
      h2fr Div.stP (by decide) (by decide) (by decide) (by decide) (by decide),
      h1fr Div.stP (by decide) (by decide)]
  have h4Y : s4.stk Div.stY = s.stk Div.stY := by
    rw [h4fr Div.stY (by decide), h3fr Div.stY (by decide) (by decide),
      h2fr Div.stY (by decide) (by decide) (by decide) (by decide) (by decide),
      h1fr Div.stY (by decide) (by decide)]
  -- a small helper for reading stacks of a `get`-updated state
  have upd_ne : ∀ (t : State) (k : Stk) (l : List Glyph) (j : Stk), j ≠ k →
      (⟨t.reg, Function.update t.stk k l⟩ : State).stk j = t.stk j :=
    fun t k l j hj => Function.update_of_ne hj l t.stk
  by_cases hbor : bv > 2 * rv + d.toNat
  · -- the borrow case: the quotient bit is `false` and the window is left unchanged
    have h4cT : s4.reg Div.rgC = Glyph.bit true := by rw [h4c]; simp [hbor]
    let s5 : State := ⟨(s4.updReg Div.rgS (Glyph.bit false)).reg,
      Function.update s4.stk Div.stQ (Glyph.bit false :: s4.stk Div.stQ)⟩
    have e5a : Eval main (.set Div.rgS (Glyph.bit false)) s4
        (s4.updReg Div.rgS (Glyph.bit false)) 1 := Eval.set_eq
    have e5b : Eval main (.push Div.stQ Div.rgS) (s4.updReg Div.rgS (Glyph.bit false)) s5 1 := by
      have h := Eval.push (main := main) Div.stQ Div.rgS (s4.updReg Div.rgS (Glyph.bit false))
      simpa [s5, State.updStk, State.updReg, Function.update_apply] using h
    have e5 : Eval main (Div.seqs [.set Div.rgS (Glyph.bit false), .push Div.stQ Div.rgS]) s4 s5 3 :=
      Div.eval_seqs_cons e5a (Div.eval_seqs_cons e5b (by rw [Div.seqs_nil]; exact Eval.skip s5))
    have hit1 : Eval main (.ite Div.rgC (Glyph.bit true)
        (Div.seqs [.set Div.rgS (Glyph.bit false), .push Div.stQ Div.rgS])
        (Div.seqs [.set Div.rgS (Glyph.bit true), .push Div.stQ Div.rgS])) s4 s5 4 :=
      Eval.iteT h4cT e5
    have h5Q : s5.stk Div.stQ = Glyph.bit false :: s4.stk Div.stQ := by
      show Function.update s4.stk Div.stQ (Glyph.bit false :: s4.stk Div.stQ) Div.stQ = _
      rw [Function.update_self]
    have h5fr : ∀ j, j ≠ Div.stQ → s5.stk j = s4.stk j := by
      intro j hj
      show Function.update s4.stk Div.stQ (Glyph.bit false :: s4.stk Div.stQ) j = s4.stk j
      rw [Function.update_of_ne hj]
    have h5D : s5.stk Div.stD = bitsG (padBits (2 * rv + d.toNat) L).reverse ++ [gD] ++
        b0.stk Div.stD := by rw [h5fr Div.stD (by decide), h4D]
    have h5R : s5.stk Div.stR = b0.stk Div.stR := by rw [h5fr Div.stR (by decide), h4R]
    -- move the unchanged window back onto `stR`
    have hlD : (bitsG (padBits (2 * rv + d.toNat) L).reverse).reverse =
        bitsG (padBits (2 * rv + d.toNat) L) := by
      rw [bitsG, List.map_reverse, List.reverse_reverse]
    obtain ⟨s6, n6, e6, hn6, h6D, h6R, h6fr⟩ :=
      eval_mvRev main Div.stD gD Div.stR gR Div.rgT (bitsG (padBits (2 * rv + d.toNat) L).reverse)
        (b0.stk Div.stD) (b0.stk Div.stR) s5
        (by intro g hg; rw [bitsG, List.mem_map] at hg
            obtain ⟨b, _, rfl⟩ := hg; exact fun h => nomatch h)
        (by rw [h5D]; simp) h5R (by decide)
    have h6R' : s6.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++
        b0.stk Div.stR := by
      rw [h6R, hlD, ← dstep_snd_borrow rv bv qv d hbor]
      simp
    -- restore the marker of `stD`
    let s7 : State := (s6.updReg Div.rgT gD).updStk Div.stD (gD :: s6.stk Div.stD)
    have e7 : Eval main (Div.mkG Div.stD gD) s6 s7 2 := Div.eval_mkG main Div.stD gD s6
    have h7D : s7.stk Div.stD = [gD] ++ b0.stk Div.stD := by
      show (Function.update s6.stk Div.stD (gD :: s6.stk Div.stD)) Div.stD = _
      rw [Function.update_self, h6D]
      simp
    have h7fr : ∀ j, j ≠ Div.stD → s7.stk j = s6.stk j := by
      intro j hj
      show (Function.update s6.stk Div.stD (gD :: s6.stk Div.stD)) j = s6.stk j
      rw [Function.update_of_ne hj]
    -- drop the ripple result
    have h7S : s7.stk Div.stS = bitsG (subRippleBits (padBits (2 * rv + d.toNat) L)
        (padBits bv L) false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
      rw [h7fr Div.stS (by decide), h6fr Div.stS (by decide) (by decide),
        h5fr Div.stS (by decide), h4S]
    obtain ⟨s8, n8, e8, hn8, h8S, h8fr⟩ :=
      dropReg_ev main s7 Div.stS gS Div.rgU
        (bitsG (subRippleBits (padBits (2 * rv + d.toNat) L) (padBits bv L) false).2.reverse)
        (b0.stk Div.stS)
        (by intro g hg; rw [bitsG, List.mem_map] at hg
            obtain ⟨b, _, rfl⟩ := hg; exact fun h => nomatch h)
        h7S
    -- assemble
    have h8R : s8.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++
        b0.stk Div.stR := by
      rw [h8fr Div.stR (by decide), h7fr Div.stR (by decide), h6R']
    have h8Q : s8.stk Div.stQ = bitsG (padBits (dstep bv (qv, rv) d).1 (jl + 1)) ++ [gQ] ++
        b0.stk Div.stQ := by
      have h8q : s8.stk Div.stQ = Glyph.bit false :: s4.stk Div.stQ := by
        rw [h8fr Div.stQ (by decide), h7fr Div.stQ (by decide), h6fr Div.stQ (by decide) (by decide),
          h5Q]
      have hq1 : (dstep bv (qv, rv) d).1 = 2 * qv := by
        have hd : (dstep bv (qv, rv) d).1
            = 2 * qv + (if bv ≤ 2 * rv + d.toNat then 1 else 0) := rfl
        rw [hd, if_neg (by omega)]
        omega
      have hbit : padBits (2 * qv) (jl + 1) = false :: padBits qv jl := by
        simpa using padBits_bit false (jl + 1) qv (by omega)
      rw [h8q, h4Q, hq1, hbit]
      simp
    have h8fr' : ∀ j, j ≠ Div.stR → j ≠ Div.stQ → s8.stk j = s.stk j := by
      intro j hjR hjQ
      by_cases hjB : j = Div.stB
      · subst hjB
        rw [h8fr Div.stB (by decide), h7fr Div.stB (by decide),
          h6fr Div.stB (by decide) (by decide), h5fr Div.stB (by decide),
          h4fr Div.stB (by decide), h3B', ← hB]
      by_cases hjS : j = Div.stS
      · subst hjS
        rw [h8S, ← hS5]
      by_cases hjC : j = Div.stC
      · subst hjC
        rw [h8fr Div.stC (by decide), h7fr Div.stC (by decide),
          h6fr Div.stC (by decide) (by decide), h5fr Div.stC (by decide), h4C, ← hS6]
      by_cases hjD : j = Div.stD
      · subst hjD
        rw [h8fr Div.stD (by decide), h7D, ← hS7]
      by_cases hjX : j = Div.stX
      · subst hjX
        rw [h8fr Div.stX (by decide), h7fr Div.stX (by decide),
          h6fr Div.stX (by decide) (by decide), h5fr Div.stX (by decide),
          h4fr Div.stX (by decide), h3fr Div.stX (by decide) (by decide),
          h2fr Div.stX (by decide) (by decide) (by decide) (by decide) (by decide),
          h1X, hS8]
      rw [h8fr j hjS, h7fr j hjD, h6fr j hjD hjR, h5fr j hjQ,
        h4fr j hjC, h3fr j hjC hjB, h2fr j hjR hjB hjS hjC hjD, h1fr j hjR hjX]
    refine ⟨s8, n1 + (n2 + (n3 + (2 + (4 + (n6 + (2 + (n8 + 1)) + 1 + 1))))), ?_, ?_, h8R, h8Q,
      h8fr'⟩
    · have hmw : Div.mainWork = Div.seqs [Div.shiftR, Div.rippleMain,
          mvRev Div.stC gC Div.stB gB Div.rgT, Div.mkG Div.stC gC,
          .ite Div.rgC (Glyph.bit true)
            (Div.seqs [.set Div.rgS (Glyph.bit false), .push Div.stQ Div.rgS])
            (Div.seqs [.set Div.rgS (Glyph.bit true), .push Div.stQ Div.rgS]),
          .ite Div.rgC (Glyph.bit true)
            (Div.seqs [mvRev Div.stD gD Div.stR gR Div.rgT, Div.mkG Div.stD gD,
              Div.dropReg Div.stS gS Div.rgU])
            (Div.seqs [mvRev Div.stS gS Div.stR gR Div.rgT, Div.mkG Div.stS gS,
              Div.dropReg Div.stD gD Div.rgU])] := rfl
      rw [hmw]
      have hit2 : Eval main (.ite Div.rgC (Glyph.bit true)
          (Div.seqs [mvRev Div.stD gD Div.stR gR Div.rgT, Div.mkG Div.stD gD,
            Div.dropReg Div.stS gS Div.rgU])
          (Div.seqs [mvRev Div.stS gS Div.stR gR Div.rgT, Div.mkG Div.stS gS,
            Div.dropReg Div.stD gD Div.rgU])) s5 s8 (n6 + (2 + (n8 + 1)) + 1) :=
        Eval.iteT h4cT
          (Div.eval_seqs_cons e6 (Div.eval_seqs_cons e7 (Div.eval_seqs_cons e8
            (Eval.skip s8))))
      exact Div.eval_seqs_cons e1 (Div.eval_seqs_cons e2 (Div.eval_seqs_cons e3
        (Div.eval_seqs_cons e4 (Div.eval_seqs_cons hit1 (Div.eval_seqs_cons hit2
          (Eval.skip s8))))))
    · have hlen3 : (bitsG (padBits bv L).reverse).length = L := by
        rw [bitsG, List.length_map, List.length_reverse, padBits_length]
      have hlen6 : (bitsG (padBits (2 * rv + d.toNat) L).reverse).length = L := by
        rw [bitsG, List.length_map, List.length_reverse, padBits_length]
      have hlen8 : (bitsG (subRippleBits (padBits (2 * rv + d.toNat) L)
          (padBits bv L) false).2.reverse).length = L := by
        rw [hsub, bitsG, List.length_map, List.length_reverse, padBits_length]
      omega
  · -- the no-borrow case: the quotient bit is `true` and the ripple result is kept
    have hbor' : bv ≤ 2 * rv + d.toNat := by omega
    have h4cF : s4.reg Div.rgC ≠ Glyph.bit true := by
      rw [h4c]; simp [show ¬ (bv > 2 * rv + d.toNat) from not_lt.mpr hbor']
    let s5 : State := ⟨(s4.updReg Div.rgS (Glyph.bit true)).reg,
      Function.update s4.stk Div.stQ (Glyph.bit true :: s4.stk Div.stQ)⟩
    have e5a : Eval main (.set Div.rgS (Glyph.bit true)) s4
        (s4.updReg Div.rgS (Glyph.bit true)) 1 := Eval.set_eq
    have e5b : Eval main (.push Div.stQ Div.rgS) (s4.updReg Div.rgS (Glyph.bit true)) s5 1 := by
      have h := Eval.push (main := main) Div.stQ Div.rgS (s4.updReg Div.rgS (Glyph.bit true))
      simpa [s5, State.updStk, State.updReg, Function.update_apply] using h
    have e5 : Eval main (Div.seqs [.set Div.rgS (Glyph.bit true), .push Div.stQ Div.rgS]) s4 s5 3 :=
      Div.eval_seqs_cons e5a (Div.eval_seqs_cons e5b (by rw [Div.seqs_nil]; exact Eval.skip s5))
    have hit1 : Eval main (.ite Div.rgC (Glyph.bit true)
        (Div.seqs [.set Div.rgS (Glyph.bit false), .push Div.stQ Div.rgS])
        (Div.seqs [.set Div.rgS (Glyph.bit true), .push Div.stQ Div.rgS])) s4 s5 4 :=
      Eval.iteF h4cF e5
    have h5Q : s5.stk Div.stQ = Glyph.bit true :: s4.stk Div.stQ := by
      show Function.update s4.stk Div.stQ (Glyph.bit true :: s4.stk Div.stQ) Div.stQ = _
      rw [Function.update_self]
    have h5fr : ∀ j, j ≠ Div.stQ → s5.stk j = s4.stk j := by
      intro j hj
      show Function.update s4.stk Div.stQ (Glyph.bit true :: s4.stk Div.stQ) j = s4.stk j
      rw [Function.update_of_ne hj]
    have h5S : s5.stk Div.stS = bitsG (subRippleBits (padBits (2 * rv + d.toNat) L)
        (padBits bv L) false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
      rw [h5fr Div.stS (by decide), h4S]
    have h5R : s5.stk Div.stR = b0.stk Div.stR := by rw [h5fr Div.stR (by decide), h4R]
    -- move the ripple result onto `stR`
    have h5res : (subRippleBits (padBits (2 * rv + d.toNat) L) (padBits bv L) false).2 =
        padBits (dstep bv (qv, rv) d).2 L := by
      rw [hsub]
      exact dstep_snd_eq rv bv qv d L (shiftWindow_lt rv bv d L hbv hrv hL) hbor'
    obtain ⟨s6, n6, e6, hn6, h6S, h6R, h6fr⟩ :=
      eval_mvRev main Div.stS gS Div.stR gR Div.rgT
        (bitsG (subRippleBits (padBits (2 * rv + d.toNat) L) (padBits bv L) false).2.reverse)
        (b0.stk Div.stS) (b0.stk Div.stR) s5
        (by intro g hg; rw [bitsG, List.mem_map] at hg
            obtain ⟨b, _, rfl⟩ := hg; exact fun h => nomatch h)
        (by rw [h5S]; simp) h5R (by decide)
    have hlS : (bitsG (subRippleBits (padBits (2 * rv + d.toNat) L) (padBits bv L)
        false).2.reverse).reverse =
        bitsG (padBits (dstep bv (qv, rv) d).2 L) := by
      rw [bitsG, List.map_reverse, List.reverse_reverse, h5res]
    have h6R' : s6.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++
        b0.stk Div.stR := by
      rw [h6R, hlS]
      simp
    -- restore the marker of `stS`
    let s7 : State := (s6.updReg Div.rgT gS).updStk Div.stS (gS :: s6.stk Div.stS)
    have e7 : Eval main (Div.mkG Div.stS gS) s6 s7 2 := Div.eval_mkG main Div.stS gS s6
    have h7S : s7.stk Div.stS = [gS] ++ b0.stk Div.stS := by
      show (Function.update s6.stk Div.stS (gS :: s6.stk Div.stS)) Div.stS = _
      rw [Function.update_self, h6S]
      simp
    have h7fr : ∀ j, j ≠ Div.stS → s7.stk j = s6.stk j := by
      intro j hj
      show (Function.update s6.stk Div.stS (gS :: s6.stk Div.stS)) j = s6.stk j
      rw [Function.update_of_ne hj]
    -- drop the old window
    have h7D : s7.stk Div.stD = bitsG (padBits (2 * rv + d.toNat) L).reverse ++ [gD] ++
        b0.stk Div.stD := by
      rw [h7fr Div.stD (by decide), h6fr Div.stD (by decide) (by decide),
        h5fr Div.stD (by decide), h4D]
    obtain ⟨s8, n8, e8, hn8, h8D, h8fr⟩ :=
      dropReg_ev main s7 Div.stD gD Div.rgU (bitsG (padBits (2 * rv + d.toNat) L).reverse)
        (b0.stk Div.stD)
        (by intro g hg; rw [bitsG, List.mem_map] at hg
            obtain ⟨b, _, rfl⟩ := hg; exact fun h => nomatch h)
        h7D
    have h8D : s8.stk Div.stD = [gD] ++ b0.stk Div.stD := h8D
    have h8R : s8.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++
        b0.stk Div.stR := by
      rw [h8fr Div.stR (by decide), h7fr Div.stR (by decide), h6R']
    have h8Q : s8.stk Div.stQ = bitsG (padBits (dstep bv (qv, rv) d).1 (jl + 1)) ++ [gQ] ++
        b0.stk Div.stQ := by
      have h8q : s8.stk Div.stQ = Glyph.bit true :: s4.stk Div.stQ := by
        rw [h8fr Div.stQ (by decide), h7fr Div.stQ (by decide), h6fr Div.stQ (by decide) (by decide),
          h5Q]
      have hq1 : (dstep bv (qv, rv) d).1 = 2 * qv + 1 := by
        have hd : (dstep bv (qv, rv) d).1
            = 2 * qv + (if bv ≤ 2 * rv + d.toNat then 1 else 0) := rfl
        rw [hd, if_pos hbor']
      have hbit : padBits (2 * qv + 1) (jl + 1) = true :: padBits qv jl := by
        simpa using padBits_bit true (jl + 1) qv (by omega)
      rw [h8q, h4Q, hq1, hbit]
      simp
    have h8fr' : ∀ j, j ≠ Div.stR → j ≠ Div.stQ → s8.stk j = s.stk j := by
      intro j hjR hjQ
      by_cases hjB : j = Div.stB
      · subst hjB
        rw [h8fr Div.stB (by decide), h7fr Div.stB (by decide),
          h6fr Div.stB (by decide) (by decide), h5fr Div.stB (by decide),
          h4fr Div.stB (by decide), h3B', ← hB]
      by_cases hjS : j = Div.stS
      · subst hjS
        rw [h8fr Div.stS (by decide), h7S, ← hS5]
      by_cases hjC : j = Div.stC
      · subst hjC
        rw [h8fr Div.stC (by decide), h7fr Div.stC (by decide),
          h6fr Div.stC (by decide) (by decide), h5fr Div.stC (by decide), h4C, ← hS6]
      by_cases hjD : j = Div.stD
      · subst hjD
        rw [h8D, ← hS7]
      by_cases hjX : j = Div.stX
      · subst hjX
        rw [h8fr Div.stX (by decide), h7fr Div.stX (by decide),
          h6fr Div.stX (by decide) (by decide), h5fr Div.stX (by decide),
          h4fr Div.stX (by decide), h3fr Div.stX (by decide) (by decide),
          h2fr Div.stX (by decide) (by decide) (by decide) (by decide) (by decide),
          h1X, hS8]
      rw [h8fr j hjD, h7fr j hjS, h6fr j hjS hjR, h5fr j hjQ,
        h4fr j hjC, h3fr j hjC hjB, h2fr j hjR hjB hjS hjC hjD, h1fr j hjR hjX]
    refine ⟨s8, n1 + (n2 + (n3 + (2 + (4 + (n6 + (2 + (n8 + 1)) + 1 + 1))))), ?_, ?_, h8R, h8Q,
      h8fr'⟩
    · have hmw : Div.mainWork = Div.seqs [Div.shiftR, Div.rippleMain,
          mvRev Div.stC gC Div.stB gB Div.rgT, Div.mkG Div.stC gC,
          .ite Div.rgC (Glyph.bit true)
            (Div.seqs [.set Div.rgS (Glyph.bit false), .push Div.stQ Div.rgS])
            (Div.seqs [.set Div.rgS (Glyph.bit true), .push Div.stQ Div.rgS]),
          .ite Div.rgC (Glyph.bit true)
            (Div.seqs [mvRev Div.stD gD Div.stR gR Div.rgT, Div.mkG Div.stD gD,
              Div.dropReg Div.stS gS Div.rgU])
            (Div.seqs [mvRev Div.stS gS Div.stR gR Div.rgT, Div.mkG Div.stS gS,
              Div.dropReg Div.stD gD Div.rgU])] := rfl
      rw [hmw]
      have hit2 : Eval main (.ite Div.rgC (Glyph.bit true)
          (Div.seqs [mvRev Div.stD gD Div.stR gR Div.rgT, Div.mkG Div.stD gD,
            Div.dropReg Div.stS gS Div.rgU])
          (Div.seqs [mvRev Div.stS gS Div.stR gR Div.rgT, Div.mkG Div.stS gS,
            Div.dropReg Div.stD gD Div.rgU])) s5 s8 (n6 + (2 + (n8 + 1)) + 1) :=
        Eval.iteF h4cF
          (Div.eval_seqs_cons e6 (Div.eval_seqs_cons e7 (Div.eval_seqs_cons e8
            (Eval.skip s8))))
      exact Div.eval_seqs_cons e1 (Div.eval_seqs_cons e2 (Div.eval_seqs_cons e3
        (Div.eval_seqs_cons e4 (Div.eval_seqs_cons hit1 (Div.eval_seqs_cons hit2
          (Eval.skip s8))))))
    · have hlen3 : (bitsG (padBits bv L).reverse).length = L := by
        rw [bitsG, List.length_map, List.length_reverse, padBits_length]
      have hlen6 : (bitsG (subRippleBits (padBits (2 * rv + d.toNat) L)
          (padBits bv L) false).2.reverse).length = L := by
        rw [hsub, bitsG, List.length_map, List.length_reverse, padBits_length]
      have hlen8 : (bitsG (padBits (2 * rv + d.toNat) L).reverse).length = L := by
        rw [bitsG, List.length_map, List.length_reverse, padBits_length]
      omega

end Work.IntLib

namespace Work.IntLib

open HvdH

/-! ## The bit iteration of the main loop -/

theorem mainStep_bit_ev (main : Cmd) (s b0 : State) (d : Bool) (sfx : List Bool)
    (bv rv qv jl L : ℕ) (hbv : 0 < bv) (hrv : rv < bv) (hL : L = bv.size + 1)
    (hP : s.stk Div.stP = bitsG (d :: sfx) ++ [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv jl) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : s.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : s.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : s.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hrl : s.reg rLoop = Glyph.eos) :
    ∃ s' n, Eval main Div.mainStep s s' n ∧ n ≤ 150 * (L + 1) + 5 ∧
      s'.stk Div.stP = bitsG sfx ++ [gP] ++ b0.stk Div.stP ∧
      s'.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++ b0.stk Div.stR ∧
      s'.stk Div.stQ = bitsG (padBits (dstep bv (qv, rv) d).1 (jl + 1)) ++ [gQ] ++ b0.stk Div.stQ ∧
      (∀ j, j ≠ Div.stP → j ≠ Div.stR → j ≠ Div.stQ → s'.stk j = s.stk j) ∧
      s'.reg rLoop = Glyph.eos := by
  set s1 : State := State.tPop s Div.stP rLoop with hs1
  have e1 : Eval main (.pop Div.stP rLoop) s s1 1 := by rw [hs1]; exact Eval.pop _ _ _
  have h1P : s1.stk Div.stP = bitsG sfx ++ [gP] ++ b0.stk Div.stP := by
    rw [hs1]
    show (Function.update s.stk Div.stP (s.stk Div.stP).tail) Div.stP = _
    rw [Function.update_self, hP]
    simp
  have h1rl : s1.reg rLoop = Glyph.bit d := by
    rw [hs1]
    show Function.update s.reg rLoop ((s.stk Div.stP).headD Glyph.eos) rLoop = Glyph.bit d
    rw [Function.update_self, hP]
    rfl
  have h1fr : ∀ j, j ≠ Div.stP → s1.stk j = s.stk j := by
    intro j hj
    rw [hs1]
    show (Function.update s.stk Div.stP (s.stk Div.stP).tail) j = s.stk j
    rw [Function.update_of_ne hj]
  have h1Pne : s1.reg rLoop ≠ gP := by rw [h1rl]; exact fun h => nomatch h
  obtain ⟨s2, n2, e2, hn2, h2R, h2Q, h2fr⟩ :=
    mainWork_ev main s1 b0 d bv rv qv jl L hbv hrv hL
      (by rw [h1fr Div.stB (by decide)]; exact hB)
      (by rw [h1fr Div.stR (by decide)]; exact hR)
      (by rw [h1fr Div.stQ (by decide)]; exact hQ)
      (by rw [h1fr Div.stS (by decide)]; exact hS5)
      (by rw [h1fr Div.stC (by decide)]; exact hS6)
      (by rw [h1fr Div.stD (by decide)]; exact hS7)
      (by rw [h1fr Div.stX (by decide)]; exact hS8)
      h1rl
  set s3 : State := s2.updReg rLoop Glyph.eos with hs3
  have e3 : Eval main (.set rLoop Glyph.eos) s2 s3 1 := by rw [hs3]; exact Eval.set _ _ _
  have h3eq : s3 = ⟨Function.update s2.reg rLoop Glyph.eos, s2.stk⟩ := by
    rw [hs3]; rfl
  have h3P : s3.stk Div.stP = bitsG sfx ++ [gP] ++ b0.stk Div.stP := by
    rw [hs3]; exact h2fr Div.stP (by decide) (by decide) ▸ h1P
  have h3R : s3.stk Div.stR = bitsG (padBits (dstep bv (qv, rv) d).2 L) ++ [gR] ++
      b0.stk Div.stR := by
    rw [hs3]; exact h2R
  have h3Q : s3.stk Div.stQ = bitsG (padBits (dstep bv (qv, rv) d).1 (jl + 1)) ++ [gQ] ++
      b0.stk Div.stQ := by
    rw [hs3]; exact h2Q
  have h3rl : s3.reg rLoop = Glyph.eos := by rw [hs3]; simp [State.updReg]
  have h3fr : ∀ j, j ≠ Div.stP → j ≠ Div.stR → j ≠ Div.stQ → s3.stk j = s.stk j := by
    intro j hjP hjR hjQ
    rw [hs3]
    show s2.stk j = s.stk j
    rw [h2fr j hjR hjQ, h1fr j hjP]
  refine ⟨s3, 1 + (((n2 + (1 + 1)) + 1) + 1), ?_, ?_, h3P, h3R, h3Q, h3fr, h3rl⟩
  · have hstep : Div.mainStep = Div.seqs [.pop Div.stP rLoop,
        .ite rLoop gP (Div.seqs [.push Div.stP rLoop, .set rLoop (Glyph.mk 0)])
          (Div.seqs [Div.mainWork, .set rLoop Glyph.eos])] := rfl
    rw [hstep]
    have h2b : Eval main (Div.seqs [Div.mainWork, .set rLoop Glyph.eos]) s1 s3 (n2 + (1 + 1)) :=
      Div.eval_seqs_cons e2 (Div.eval_seqs_cons e3 (by rw [Div.seqs_nil]; exact Eval.skip s3))
    have hite : Eval main (.ite rLoop gP (Div.seqs [.push Div.stP rLoop, .set rLoop (Glyph.mk 0)])
        (Div.seqs [Div.mainWork, .set rLoop Glyph.eos])) s1 s3 ((n2 + (1 + 1)) + 1) :=
      Eval.iteF h1Pne h2b
    exact Div.eval_seqs_cons e1 (Div.eval_seqs_cons hite (Eval.skip s3))
  · omega

/-- The terminal iteration of the main loop: the head of `stP` is the marker `gP`, which is pushed
back, and the loop register is set to `mk 0` (so the loop stops). -/
theorem mainStep_end_ev (main : Cmd) (s b0 : State)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP) (hrl : s.reg rLoop = Glyph.eos) :
    ∃ s' n, Eval main Div.mainStep s s' n ∧ n ≤ 6 ∧
      s'.stk Div.stP = [gP] ++ b0.stk Div.stP ∧
      (∀ j, j ≠ Div.stP → s'.stk j = s.stk j) ∧ s'.reg rLoop = Glyph.mk 0 := by
  set s1 : State := State.tPop s Div.stP rLoop with hs1
  have e1 : Eval main (.pop Div.stP rLoop) s s1 1 := by rw [hs1]; exact Eval.pop _ _ _
  have h1Pne : s1.reg rLoop = gP := by
    rw [hs1]
    show Function.update s.reg rLoop ((s.stk Div.stP).headD Glyph.eos) rLoop = gP
    rw [Function.update_self, hP]
    rfl
  set s2 : State := s1.updStk Div.stP (s1.reg rLoop :: s1.stk Div.stP) with hs2
  have e2 : Eval main (.push Div.stP rLoop) s1 s2 1 := by rw [hs2]; exact Eval.push _ _ _
  set s3 : State := s2.updReg rLoop (Glyph.mk 0) with hs3
  have e3 : Eval main (.set rLoop (Glyph.mk 0)) s2 s3 1 := by rw [hs3]; exact Eval.set _ _ _
  have h1Pstk : s1.stk Div.stP = b0.stk Div.stP := by
    rw [hs1]
    show (Function.update s.stk Div.stP (s.stk Div.stP).tail) Div.stP = b0.stk Div.stP
    rw [Function.update_self, hP]
    rfl
  have h2P : s2.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [hs2]
    show (s1.updStk Div.stP (s1.reg rLoop :: s1.stk Div.stP)).stk Div.stP = _
    rw [State.updStk_apply, if_pos rfl, h1Pne, h1Pstk]
    simp
  have h3P : s3.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [hs3]; exact h2P
  have h3rl : s3.reg rLoop = Glyph.mk 0 := by rw [hs3]; simp [State.updReg]
  have h3fr : ∀ j, j ≠ Div.stP → s3.stk j = s.stk j := by
    intro j hj
    rw [hs3]
    show s2.stk j = s.stk j
    rw [hs2]
    show (Function.update s1.stk Div.stP (s1.reg rLoop :: s1.stk Div.stP)) j = s.stk j
    rw [Function.update_of_ne hj]
    rw [hs1]
    show (Function.update s.stk Div.stP (s.stk Div.stP).tail) j = s.stk j
    rw [Function.update_of_ne hj]
  refine ⟨s3, 1 + (((1 + (1 + 1)) + 1) + 1), ?_, ?_, h3P, h3fr, h3rl⟩
  · have hstep : Div.mainStep = Div.seqs [.pop Div.stP rLoop,
        .ite rLoop gP (Div.seqs [.push Div.stP rLoop, .set rLoop (Glyph.mk 0)])
          (Div.seqs [Div.mainWork, .set rLoop Glyph.eos])] := rfl
    rw [hstep]
    have h2b : Eval main (Div.seqs [.push Div.stP rLoop, .set rLoop (Glyph.mk 0)]) s1 s3
        (1 + (1 + 1)) :=
      Div.eval_seqs_cons e2 (Div.eval_seqs_cons e3 (by rw [Div.seqs_nil]; exact Eval.skip s3))
    have hite : Eval main (.ite rLoop gP (Div.seqs [.push Div.stP rLoop, .set rLoop (Glyph.mk 0)])
        (Div.seqs [Div.mainWork, .set rLoop Glyph.eos])) s1 s3 ((1 + (1 + 1)) + 1) :=
      Eval.iteT h1Pne h2b
    exact Div.eval_seqs_cons e1 (Div.eval_seqs_cons hite (Eval.skip s3))
  · omega

/-! ## The invariant of the main loop -/

/-- The number of bits at the head of a list of glyphs. -/
def nBit : List Glyph → ℕ
  | [] => 0
  | Glyph.bit _ :: l => nBit l + 1
  | _ :: _ => 0

theorem nBit_bitsG (l : List Bool) (t : List Glyph) : nBit (bitsG l ++ [gP] ++ t) = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have h : bitsG (b :: l) ++ [gP] ++ t = Glyph.bit b :: (bitsG l ++ [gP] ++ t) := by
      simp [bitsG, List.append_assoc]
    rw [h]
    show nBit (bitsG l ++ [gP] ++ t) + 1 = (b :: l).length
    rw [ih, List.length_cons]

theorem nBit_marker (t : List Glyph) : nBit ([gP] ++ t) = 0 := rfl

/-- The measure of the main loop. -/
def lmeas (s : State) : ℕ :=
  nBit (s.stk Div.stP) + (if s.reg rLoop = Glyph.eos then 1 else 0)

theorem lmeas_of (A : List Bool) (b0 : State) (s : State) (i : ℕ)
    (hP : s.stk Div.stP = bitsG (A.drop i) ++ [gP] ++ b0.stk Div.stP)
    (hrl : s.reg rLoop = Glyph.eos) : lmeas s = A.length - i + 1 := by
  rw [lmeas, hP, nBit_bitsG, List.length_drop, if_pos hrl]

theorem lmeas_end (b0 : State) (s : State)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP) (hrl : s.reg rLoop = Glyph.mk 0) :
    lmeas s = 0 := by
  rw [lmeas, hP, nBit_marker]
  simp [hrl]

/-- The state description of the main loop after `i` iterations (the loop register is `g`). -/
def psi (S b0 : State) (A : List Bool) (bv qv rv j L i : ℕ) (g : Glyph) (s : State) : Prop :=
  s.stk Div.stP = bitsG (A.drop i) ++ [gP] ++ b0.stk Div.stP ∧
  s.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB ∧
  s.stk Div.stR = bitsG (padBits ((A.take i).foldl (dstep bv) (qv, rv)).2 L) ++ [gR] ++
    b0.stk Div.stR ∧
  s.stk Div.stQ = bitsG (padBits ((A.take i).foldl (dstep bv) (qv, rv)).1 (j + i)) ++ [gQ] ++
    b0.stk Div.stQ ∧
  s.stk Div.stS = [gS] ++ b0.stk Div.stS ∧
  s.stk Div.stC = [gC] ++ b0.stk Div.stC ∧
  s.stk Div.stD = [gD] ++ b0.stk Div.stD ∧
  s.stk Div.stX = [gX] ++ b0.stk Div.stX ∧
  s.stk Div.stY = S.stk Div.stY ∧
  (∀ k, k ≠ Div.stP → k ≠ Div.stB → k ≠ Div.stR → k ≠ Div.stQ → k ≠ Div.stS →
    k ≠ Div.stC → k ≠ Div.stD → k ≠ Div.stX → s.stk k = S.stk k) ∧
  s.reg rLoop = g

/-- The invariant of the main loop. -/
def loopInv (S b0 : State) (A : List Bool) (bv qv rv j L : ℕ) (s : State) : Prop :=
  (∃ i, i ≤ A.length ∧ psi S b0 A bv qv rv j L i Glyph.eos s) ∨
    psi S b0 A bv qv rv j L A.length (Glyph.mk 0) s

end Work.IntLib

namespace Work.IntLib

open HvdH

/-- The main loop: unrolling `Div.mainLoopProg` from the state family at `0` to the terminal state. -/
theorem mainLoop_ev (main : Cmd) (S b0 : State) (A : List Bool) (bv qv rv j L : ℕ)
    (hbv : 0 < bv) (hrv : rv < bv) (hL : L = bv.size + 1)
    (hS : S = mSt S b0 A bv qv rv j L 0) :
    ∃ s' n, Eval main Div.mainLoopProg S s' n ∧
      n ≤ (A.length + 1) * (150 * (L + 1) + 6) + 3 ∧
      s'.stk Div.stP = [gP] ++ b0.stk Div.stP ∧
      s'.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB ∧
      s'.stk Div.stR = bitsG (padBits (A.foldl (dstep bv) (qv, rv)).2 L) ++ [gR] ++ b0.stk Div.stR ∧
      s'.stk Div.stQ = bitsG (padBits (A.foldl (dstep bv) (qv, rv)).1 (j + A.length)) ++ [gQ] ++
        b0.stk Div.stQ ∧
      s'.stk Div.stS = [gS] ++ b0.stk Div.stS ∧
      s'.stk Div.stC = [gC] ++ b0.stk Div.stC ∧
      s'.stk Div.stD = [gD] ++ b0.stk Div.stD ∧
      s'.stk Div.stX = [gX] ++ b0.stk Div.stX ∧
      s'.stk Div.stY = S.stk Div.stY ∧
      (∀ k, k ≠ Div.stP → k ≠ Div.stB → k ≠ Div.stR → k ≠ Div.stQ → k ≠ Div.stS →
        k ≠ Div.stC → k ≠ Div.stD → k ≠ Div.stX → k ≠ Div.stY → s'.stk k = S.stk k) := by
  have hSrl : S.reg rLoop = Glyph.eos := by rw [hS]; simp
  have hset : Eval main (.set rLoop Glyph.eos) S S 1 := by
    have h := Eval.set (main := main) rLoop Glyph.eos S
    rw [State.reg_update_eq hSrl] at h
    exact h
  -- the initial state satisfies the invariant
  have hInv0 : loopInv S b0 A bv qv rv j L S := by
    left
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; exact mSt_stkP S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkB S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkR S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkQ S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkS S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkC S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkD S b0 A bv qv rv j L 0
    · rw [hS]; exact mSt_stkX S b0 A bv qv rv j L 0
    · rfl
    · intro k _ _ _ _ _ _ _ _
      rfl
    · exact hSrl
  have hpos : ∀ s, loopInv S b0 A bv qv rv j L s → s.reg rLoop = Glyph.eos → 0 < lmeas s := by
    intro s hinv hrl
    rcases hinv with ⟨i, hi, hpsi⟩ | hpsi
    · rcases hpsi with ⟨hP, _⟩
      rw [lmeas_of A b0 s i hP hrl]
      omega
    · rcases hpsi with ⟨_, _, _, _, _, _, _, _, _, _, hreg⟩
      rw [hreg] at hrl
      exact absurd hrl (by decide)
  have hstep : ∀ s, loopInv S b0 A bv qv rv j L s → s.reg rLoop = Glyph.eos →
      ∃ s' n, Eval main Div.mainStep s s' n ∧ n ≤ 150 * (L + 1) + 5 ∧
        loopInv S b0 A bv qv rv j L s' ∧ lmeas s' < lmeas s := by
    intro s hinv hrl
    rcases hinv with ⟨i, hi, hpsi⟩ | hpsi
    · rcases hpsi with ⟨hP, hB, hR, hQ, hS5, hS6, hS7, hS8, hS9, hfr, hreg⟩
      by_cases hilt : i < A.length
      · have hdrop : A.drop i = A.getD i false :: A.drop (i + 1) := by
          rw [List.drop_eq_getElem_cons hilt, List.getD_eq_getElem A false hilt]
        have hP' : s.stk Div.stP = bitsG (A.getD i false :: A.drop (i + 1)) ++ [gP] ++
            b0.stk Div.stP := by rw [← hdrop]; exact hP
        have hfold : (A.take (i + 1)).foldl (dstep bv) (qv, rv) =
            dstep bv ((A.take i).foldl (dstep bv) (qv, rv)) (A.getD i false) := by
          rw [take_succ_eq_concat_getD A i hilt, List.foldl_append]
          rfl
        obtain ⟨s', n, hev, hn, hP'', hR'', hQ'', hfr', hrl'⟩ :=
          mainStep_bit_ev main s b0 (A.getD i false) (A.drop (i + 1)) bv
            ((A.take i).foldl (dstep bv) (qv, rv)).2 ((A.take i).foldl (dstep bv) (qv, rv)).1
            (j + i) L hbv (fold_dstep_lt (A.take i) bv qv rv hbv hrv) hL hP' hB hR hQ hS5 hS6
            hS7 hS8 hreg
        refine ⟨s', n, hev, hn, ?_, ?_⟩
        · left
          refine ⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hP'']
          · rw [hfr' Div.stB (by decide) (by decide) (by decide), hB]
          · rw [hR'', ← hfold]
          · rw [hQ'', ← hfold, show j + (i + 1) = (j + i) + 1 from by omega]
          · rw [hfr' Div.stS (by decide) (by decide) (by decide), hS5]
          · rw [hfr' Div.stC (by decide) (by decide) (by decide), hS6]
          · rw [hfr' Div.stD (by decide) (by decide) (by decide), hS7]
          · rw [hfr' Div.stX (by decide) (by decide) (by decide), hS8]
          · rw [hfr' Div.stY (by decide) (by decide) (by decide), hS9]
          · intro k h1 h2 h3 h4 h5 h6 h7 h8
            rw [hfr' k h1 h3 h4, hfr k h1 h2 h3 h4 h5 h6 h7 h8]
          · exact hrl'
        · rw [lmeas_of A b0 s' (i + 1) hP'' hrl', lmeas_of A b0 s i hP hreg]
          omega
      · have hiN : i = A.length := by omega
        subst hiN
        have hP' : s.stk Div.stP = [gP] ++ b0.stk Div.stP := by
          rw [hP, List.drop_length]
          rfl
        obtain ⟨s', n, hev, hn, hP'', hfr', hrl'⟩ := mainStep_end_ev main s b0 hP' hreg
        refine ⟨s', n, hev, by omega, ?_, ?_⟩
        · right
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hP'', List.drop_length]; rfl
          · rw [hfr' Div.stB (by decide), hB]
          · rw [hfr' Div.stR (by decide), hR]
          · rw [hfr' Div.stQ (by decide), hQ]
          · rw [hfr' Div.stS (by decide), hS5]
          · rw [hfr' Div.stC (by decide), hS6]
          · rw [hfr' Div.stD (by decide), hS7]
          · rw [hfr' Div.stX (by decide), hS8]
          · rw [hfr' Div.stY (by decide), hS9]
          · intro k h1 h2 h3 h4 h5 h6 h7 h8
            rw [hfr' k h1, hfr k h1 h2 h3 h4 h5 h6 h7 h8]
          · exact hrl'
        · rw [lmeas_end b0 s' hP'' hrl', lmeas_of A b0 s A.length hP hreg]
          omega
    · rcases hpsi with ⟨_, _, _, _, _, _, _, _, _, _, hreg⟩
      rw [hreg] at hrl
      exact absurd hrl (by decide)
  obtain ⟨sfin, m, hev, hinv, hnot, hm⟩ :=
    loop_measure rLoop Glyph.eos Div.mainStep (loopInv S b0 A bv qv rv j L) lmeas
      (150 * (L + 1) + 5) hpos hstep S hInv0 hSrl
  rcases hinv with ⟨i, hi, hpsi⟩ | hpsi
  · rcases hpsi with ⟨_, _, _, _, _, _, _, _, _, _, hreg⟩
    exact absurd (by rw [hreg]) hnot
  · rcases hpsi with ⟨hP, hB, hR, hQ, hS5, hS6, hS7, hS8, hS9, hfr, hreg⟩
    have hmeas : m ≤ (A.length + 1) * (150 * (L + 1) + 6) + 1 := by
      have h1 : lmeas S = A.length + 1 := by
        refine lmeas_of A b0 S 0 ?_ hSrl
        rw [hS]; exact mSt_stkP S b0 A bv qv rv j L 0
      rw [h1] at hm
      omega
    have hS9b : S.stk Div.stY = b0.stk Div.stY := by
      rw [hS]; exact mSt_stkY S b0 A bv qv rv j L 0
    have hfr9 : ∀ k, k ≠ Div.stP → k ≠ Div.stB → k ≠ Div.stR → k ≠ Div.stQ → k ≠ Div.stS →
        k ≠ Div.stC → k ≠ Div.stD → k ≠ Div.stX → k ≠ Div.stY → sfin.stk k = S.stk k := by
      intro k h1 h2 h3 h4 h5 h6 h7 h8 h9
      by_cases hY : k = Div.stY
      · subst hY; exact hS9
      · exact hfr k h1 h2 h3 h4 h5 h6 h7 h8
    refine ⟨sfin, 1 + (m + 1), ?_, ?_, ?_, hB, ?_, ?_, hS5, hS6, hS7, hS8, ?_, hfr9⟩
    · have : Div.mainLoopProg =
          Div.seqs [.set rLoop Glyph.eos, .loop rLoop Glyph.eos Div.mainStep] := rfl
      rw [this]
      exact Div.eval_seqs_cons hset (Div.eval_seqs_cons hev
        (by rw [Div.seqs_nil]; exact Eval.skip sfin))
    · omega
    · rw [hP, List.drop_length]; rfl
    · rw [hR, List.take_length]
    · rw [hQ, List.take_length]
    · rw [hS9, hS9b]

end Work.IntLib

namespace Work.IntLib

open HvdH

/-! ## The main loop specification -/

theorem div_mainLoop (main : HvdH.Cmd) (b0 : HvdH.State) (A : List Bool) (bv rv qv j m : ℕ)
    (L : ℕ) (hbv : 0 < bv) (hrv : rv < bv) (hL : L = bv.size + 1) (hA : A.length = m)
    (hqv : bv * qv + rv = Work.IntLib.bval (A.take j)) (hj : j ≤ m) (S : HvdH.State)
    (hP : S.stk Work.IntLib.Div.stP = Work.IntLib.bitsG (A.drop j) ++ [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP)
    (hB : S.stk Work.IntLib.Div.stB = Work.IntLib.bitsG (Work.IntLib.padBits bv L) ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hR : S.stk Work.IntLib.Div.stR = Work.IntLib.bitsG (Work.IntLib.padBits rv L) ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hQ : S.stk Work.IntLib.Div.stQ = Work.IntLib.bitsG (Work.IntLib.padBits qv j) ++ [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ)
    (hS5 : S.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hS6 : S.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hS7 : S.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
    (hS8 : S.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hS9 : S.stk Work.IntLib.Div.stY = b0.stk Work.IntLib.Div.stY)
    (hrl : S.reg Work.IntLib.rLoop = HvdH.Glyph.eos) :
    ∃ s' n rv' qv', HvdH.Eval main Work.IntLib.Div.mainLoopProg S s' n ∧
      n ≤ (m - j + 1) * (150 * (L + 1) + 150) ∧
      s'.stk Work.IntLib.Div.stP = [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP ∧
      s'.stk Work.IntLib.Div.stB = Work.IntLib.bitsG (Work.IntLib.padBits bv L) ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB ∧
      s'.stk Work.IntLib.Div.stR = Work.IntLib.bitsG (Work.IntLib.padBits rv' L) ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stQ = Work.IntLib.bitsG (Work.IntLib.padBits qv' m) ++ [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ ∧
      bv * qv' + rv' = Work.IntLib.bval A ∧ rv' < bv ∧
      s'.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS ∧
      s'.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC ∧
      s'.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD ∧
      s'.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX ∧
      s'.stk Work.IntLib.Div.stY = b0.stk Work.IntLib.Div.stY ∧
      (∀ j' : HvdH.Stk, j' ≠ Work.IntLib.Div.stP → j' ≠ Work.IntLib.Div.stB →
        j' ≠ Work.IntLib.Div.stR → j' ≠ Work.IntLib.Div.stQ → j' ≠ Work.IntLib.Div.stS →
        j' ≠ Work.IntLib.Div.stC → j' ≠ Work.IntLib.Div.stD → j' ≠ Work.IntLib.Div.stX →
        j' ≠ Work.IntLib.Div.stY → s'.stk j' = S.stk j') := by
  have hlenA : (A.drop j).length = m - j := by rw [List.length_drop, hA]
  have hSj : j + (m - j) = m := by omega
  -- the given state is the state family at `0`
  have hS : S = mSt S b0 (A.drop j) bv qv rv j L 0 := by
    refine State.ext_mk ?_ ?_
    · funext r
      show S.reg r = (mSt S b0 (A.drop j) bv qv rv j L 0).reg r
      by_cases hr : r = rLoop
      · subst hr
        rw [hrl, mSt_reg_rLoop]
      · rw [mSt_reg_ne S b0 (A.drop j) bv qv rv j L 0 r hr]
    · funext k
      show S.stk k = (mSt S b0 (A.drop j) bv qv rv j L 0).stk k
      by_cases h1 : k = Div.stP
      · subst h1; rw [hP, mSt_stkP, List.drop_zero]
      by_cases h2 : k = Div.stB
      · subst h2; rw [hB, mSt_stkB]
      by_cases h3 : k = Div.stR
      · subst h3
        rw [hR, mSt_stkR, List.take_zero, List.foldl_nil]
      by_cases h4 : k = Div.stQ
      · subst h4
        rw [hQ, mSt_stkQ, List.take_zero, List.foldl_nil]
        simp
      by_cases h5 : k = Div.stS
      · subst h5; rw [hS5, mSt_stkS]
      by_cases h6 : k = Div.stC
      · subst h6; rw [hS6, mSt_stkC]
      by_cases h7 : k = Div.stD
      · subst h7; rw [hS7, mSt_stkD]
      by_cases h8 : k = Div.stX
      · subst h8; rw [hS8, mSt_stkX]
      by_cases h9 : k = Div.stY
      · subst h9; rw [hS9, mSt_stkY]
      · rw [mSt_stk_ne S b0 (A.drop j) bv qv rv j L 0 k h1 h2 h3 h4 h5 h6 h7 h8 h9]
  obtain ⟨s', n, hev, hn, h1, h2, h3, h4, h5, h6, h7, h8, h9, hfr⟩ :=
    mainLoop_ev main S b0 (A.drop j) bv qv rv j L hbv hrv hL hS
  refine ⟨s', n, ((A.drop j).foldl (dstep bv) (qv, rv)).2,
    ((A.drop j).foldl (dstep bv) (qv, rv)).1, hev, ?_, h1, h2, h3, ?_, ?_, ?_, h5, h6, h7, h8,
    ?_, ?_⟩
  · have h1' : (A.drop j).length + 1 = m - j + 1 := by rw [hlenA]
    rw [h1'] at hn
    have : (m - j + 1) * (150 * (L + 1) + 6) + 3 ≤ (m - j + 1) * (150 * (L + 1) + 150) := by
      have h2 : 1 ≤ m - j + 1 := by omega
      nlinarith [h2]
    omega
  · rw [h4, hlenA, hSj]
  · have harith : bv * ((A.drop j).foldl (dstep bv) (qv, rv)).1 +
        ((A.drop j).foldl (dstep bv) (qv, rv)).2 = bval A := by
      rw [fold_dstep_val, List.length_drop, hA, hqv, bval_take_drop A j (by omega), hA]
    exact harith
  · exact fold_dstep_lt (A.drop j) bv qv rv hbv hrv
  · rw [h9, hS9]
  · exact hfr

end Work.IntLib
