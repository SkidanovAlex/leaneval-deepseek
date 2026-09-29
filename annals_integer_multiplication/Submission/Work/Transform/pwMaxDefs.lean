import Mathlib
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.bits_ofBits_of_isBits
import Submission.Work.Transform.pwScanDefs

/-!
# `Work.Transform.Pw`: definitions for the parameter-word max phase

The max phase reads the encoding of a list `ms` of positive integers above a frame marker `gM` on
stack `src` and leaves `encodeNat (lmax ms)` (least significant bit first) above the marker of the
empty running maximum on stack `mx`.

One element at a time (`elemProg`):

* `storeMag src sp ds` pops the element's sign onto `ds` and moves its bits (most significant
  first) above a fresh `gM` on `sp`, consuming the element's encoding up to its `iend`;
* `copyMarked2 sp spc tmp` copies those bits to `spc` (keeping `sp`), and `revMarked spc sA`
  turns them into the least-significant-first order above a fresh `gM` on `sA`;
* `scanProg sA mx bA bB` is the *buffered* lockstep comparison of `sA` against `mx`: it consumes
  `min` of the two, parks the consumed prefixes on the buffers, and records the comparison in
  `reg rFlag`;
* if the flag is `gGt` the element wins (`winProg`): drain `mx`, move the bits from `sp` onto `mx`
  (with `tLoop`, which reverses them back to least-significant-first), and restore the scratch
  stacks; otherwise the running maximum wins (`loseProg`): push the consumed prefix back from `bB`
  (restoring `mx` exactly) and restore the scratch stacks;
* `pop ds` discards the element's sign.

`loopProg` runs `bodyProg` (`cons`-dispatch plus `elemProg`) until the list's terminating `nil`.

`Scr src mx` bundles the seven scratch stacks used by the phase together with the fact that they
are pairwise distinct and different from `src` and `mx`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel

/-! ## Registers -/

/-- First scratch register of the max-phase branch programs. -/
def mA : Reg := 0

/-- Second scratch register of the max-phase branch programs. -/
def mB : Reg := 1

/-- Loop-control register of the max-phase loop. -/
def mC : Reg := 2

/-! ## The branch programs -/

/-- The `gGt` branch: the element becomes the new maximum.  Drain `mx` down to its marker, move
the element's bits from `sp` (most significant first) onto `mx` (they arrive reversed, i.e. least
significant first), then restore `sp`, `sA`, `bA`, `bB` by removing their markers/content. -/
def winProg (sp sA bA bB mx : Stk) : Cmd :=
  .seq (dropMarked sA mA mB)
   (.seq (dropMarked bA mA mB)
    (.seq (dLoop mx gM mB)
     (.seq (tLoop sp gM mx mB)
      (.seq (dropMarked sp mA mB)
            (dropMarked bB mA mB)))))

/-- The "the maximum survives" branch: push the consumed prefix of the maximum back from the buffer
`bB` onto `mx` (which restores `mx` exactly), drop the buffer's marker, and restore `sA`, `bA`,
`sp`. -/
def loseProg (sp sA bA bB mx : Stk) : Cmd :=
  .seq (tLoop bB gM mx mB)
   (.seq (.pop bB mA)
    (.seq (dropMarked sA mA mB)
     (.seq (dropMarked bA mA mB)
           (dropMarked sp mA mB))))

/-! ## One element -/

/-- One element of the max phase. -/
def elemProg (src mx sp spc ds tmp sA bA bB : Stk) : Cmd :=
  .seq (storeMag src sp ds mA mB)
   (.seq (copyMarked2 sp spc tmp mA mB)
    (.seq (revMarked spc sA mA mB)
     (.seq (scanProg sA mx bA bB)
      (.seq (.ite rFlag gGt (winProg sp sA bA bB mx) (loseProg sp sA bA bB mx))
            (.pop ds mA)))))

/-- One iteration of a max-phase loop over a `cons`-list: pop the leading glyph of `src`; a `cons`
runs `elem` (the per-element word) and continues, a `nil` stops. -/
def bodyOf (elem : Cmd) (src : Stk) : Cmd :=
  .seq (.pop src mC)
   (.ite mC Glyph.cons
     (.seq elem (.set mC Glyph.eos))
     (.set mC Glyph.iend))

/-- The loop of a max phase whose per-element word is `elem`. -/
def loopOf (elem : Cmd) (src : Stk) : Cmd :=
  .seq (.set mC Glyph.eos) (.loop mC Glyph.eos (bodyOf elem src))

/-- One iteration of the parameter-word max phase (`elemProg` as the per-element word). -/
def bodyProg (src mx sp spc ds tmp sA bA bB : Stk) : Cmd :=
  bodyOf (elemProg src mx sp spc ds tmp sA bA bB) src

/-- The parameter-word max phase loop. -/
def loopProg (src mx sp spc ds tmp sA bA bB : Stk) : Cmd :=
  loopOf (elemProg src mx sp spc ds tmp sA bA bB) src

/-- Specification of the per-element word of the max phase: from an element `t > 0` on top of `src`
and a running maximum `M` on `mx` it consumes `(Val.int t).enc`, replaces `M` by `max M t` and
restores every other stack. -/
def ElemSpec (src mx : Stk) (elem : Cmd) (Ke : ℕ) : Prop :=
  ∀ (main : Cmd) (t M : ℕ) (tail mxTail : List Glyph) (s : State),
    0 < t → s.stk src = (Val.int (t : ℤ)).enc ++ tail →
    s.stk mx = (Computability.encodeNat M).map Glyph.bit ++ gM :: mxTail →
    ∃ s' n, Eval main elem s s' n ∧ n ≤ Ke * (t.size + 1) ∧ s'.stk src = tail ∧
      s'.stk mx = (Computability.encodeNat (max M t)).map Glyph.bit ++ gM :: mxTail ∧
      (∀ j : Stk, j ≠ src → j ≠ mx → s'.stk j = s.stk j)

/-- Specification of the whole max phase (the conclusion of the target statement). -/
def MaxSpec (src mx : Stk) (prog : Cmd) (K : ℕ) : Prop :=
  ∀ (main : Cmd) (ms : List ℕ) (below mxTail : List Glyph) (s : State),
    (∀ t ∈ ms, 0 < t) → s.stk src = (intList ms).enc ++ gM :: below →
    s.stk mx = gM :: mxTail →
    ∃ s' n, Eval main prog s s' n ∧ n ≤ K * (ms.sum + 1) ∧
      s'.stk src = gM :: below ∧
      s'.stk mx = (Computability.encodeNat (lmax ms)).map Glyph.bit ++ gM :: mxTail ∧
      (∀ j : Stk, j ≠ src → j ≠ mx → s'.stk j = s.stk j)

/-! ## The seven scratch stacks -/

/-- The seven scratch stacks of the max phase, all distinct and different from `src` and `mx`. -/
structure Scr (src mx : Stk) where
  /-- Bits of the current element, most significant first, above a marker. -/
  sp : Stk
  /-- Temporary copy of `sp`. -/
  spc : Stk
  /-- The element's sign. -/
  ds : Stk
  /-- Temporary of `copyMarked2`. -/
  tmp : Stk
  /-- Bits of the current element, least significant first, above a marker. -/
  sA : Stk
  /-- Buffer of the consumed prefix of the element. -/
  bA : Stk
  /-- Buffer of the consumed prefix of the running maximum. -/
  bB : Stk
  /-- The seven scratch stacks are pairwise distinct. -/
  nodup : [sp, spc, ds, tmp, sA, bA, bB].Nodup
  /-- No scratch stack is `src`. -/
  ne_src : ∀ x ∈ [sp, spc, ds, tmp, sA, bA, bB], x ≠ src
  /-- No scratch stack is `mx`. -/
  ne_mx : ∀ x ∈ [sp, spc, ds, tmp, sA, bA, bB], x ≠ mx

/-! ## Encoding and arithmetic facts (local copies, so that this file does not have to import
`Submission.Work.Transform.pwList`, which clashes with `pwScanDefs` over `bit_ne_gM`). -/

/-- The encoding of `Val.int z`, unfolded. -/
theorem mx_enc_int (z : ℤ) : (Val.int z).enc = (if z < 0 then Glyph.neg else Glyph.pos) ::
    ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) := rfl

/-- For positive integers the sign glyph is `pos`. -/
theorem mx_enc_int_nat (t : ℕ) : (Val.int (t : ℤ)).enc = Glyph.pos ::
    ((Computability.encodeNat t).map Glyph.bit ++ [Glyph.iend]) := by
  rw [mx_enc_int]
  have h : ¬ ((t : ℤ) < 0) := by omega
  rw [if_neg h, Int.natAbs_natCast]

theorem mx_intList_cons (t : ℕ) (ts : List ℕ) :
    (intList (t :: ts)).enc = Glyph.cons :: ((Val.int (t : ℤ)).enc ++ (intList ts).enc) := rfl

theorem mx_intList_nil : (intList ([] : List ℕ)).enc = [Glyph.nil] := rfl

/-- The size of a natural is at most the natural itself, for positive naturals. -/
theorem mx_size_le_self (t : ℕ) (h : 0 < t) : t.size ≤ t := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

theorem mx_sum_size_le (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) :
    (ms.map (fun t : ℕ => t.size)).sum ≤ ms.sum := by
  induction ms with
  | nil => simp
  | cons a as ih =>
    have has : ∀ t ∈ as, 0 < t := fun t ht => h t (by simp [ht])
    have hs : a.size ≤ a := mx_size_le_self a (h a (by simp))
    have ih' := ih has
    simp only [List.map_cons, List.sum_cons] at ih' ⊢
    exact Nat.add_le_add hs ih'

theorem mx_length_le_sum (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) : ms.length ≤ ms.sum := by
  induction ms with
  | nil => simp
  | cons a as ih =>
    have has : ∀ t ∈ as, 0 < t := fun t ht => h t (by simp [ht])
    have ha : 1 ≤ a := h a (by simp)
    have ih' := ih has
    have h1 : as.length + 1 ≤ as.sum + a := Nat.add_le_add ih' ha
    simp only [List.length_cons, List.sum_cons]
    omega

theorem mx_lmax_cons (a : ℕ) (as : List ℕ) : lmax (a :: as) = max a (lmax as) := rfl

theorem mx_lmax_nil : lmax ([] : List ℕ) = 0 := rfl

theorem mx_encodeNat_zero : Computability.encodeNat 0 = [] := by
  rw [Work.IntLib.encodeNat_eq_bits]; rfl

theorem mx_encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size :=
  Work.IntLib.encodeNat_length n

theorem mx_ofBits_encodeNat (n : ℕ) : Work.IntLib.ofBits (Computability.encodeNat n) = n := by
  rw [Work.IntLib.encodeNat_eq_bits]; exact Work.IntLib.ofBits_bits n

theorem mx_isBits_encodeNat (n : ℕ) : Work.IntLib.IsBits (Computability.encodeNat n) := by
  rw [Work.IntLib.encodeNat_eq_bits]; exact Work.IntLib.isBits_bits n

/-- A strictly larger canonical bit string is at least as long. -/
theorem mx_size_le_of_lt {m t : ℕ} (h : m < t) : m.size ≤ t.size := by
  rw [← mx_encodeNat_length, ← mx_encodeNat_length]
  by_contra hc
  rw [not_le] at hc
  have := Pw.ofBits_lt_of_length_lt (mx_isBits_encodeNat t) (mx_isBits_encodeNat m) hc
  rw [mx_ofBits_encodeNat, mx_ofBits_encodeNat] at this
  omega

theorem mx_max_eq_right {m t : ℕ} (h : m < t) : max m t = t := max_eq_right (le_of_lt h)

theorem mx_max_eq_left {m t : ℕ} (h : t ≤ m) : max m t = m := max_eq_left h


/-! ## The 35 distinctness facts -/

theorem Scr.ne_sp_spc (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.spc := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_ds (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.ds := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_tmp (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.tmp := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_sA (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.sA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_bA (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.bA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_bB (src mx : Stk) (S : Scr src mx) : S.sp ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_spc_ds (src mx : Stk) (S : Scr src mx) : S.spc ≠ S.ds := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_spc_tmp (src mx : Stk) (S : Scr src mx) : S.spc ≠ S.tmp := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_spc_sA (src mx : Stk) (S : Scr src mx) : S.spc ≠ S.sA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_spc_bA (src mx : Stk) (S : Scr src mx) : S.spc ≠ S.bA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_spc_bB (src mx : Stk) (S : Scr src mx) : S.spc ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_ds_tmp (src mx : Stk) (S : Scr src mx) : S.ds ≠ S.tmp := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_ds_sA (src mx : Stk) (S : Scr src mx) : S.ds ≠ S.sA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_ds_bA (src mx : Stk) (S : Scr src mx) : S.ds ≠ S.bA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_ds_bB (src mx : Stk) (S : Scr src mx) : S.ds ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_tmp_sA (src mx : Stk) (S : Scr src mx) : S.tmp ≠ S.sA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_tmp_bA (src mx : Stk) (S : Scr src mx) : S.tmp ≠ S.bA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_tmp_bB (src mx : Stk) (S : Scr src mx) : S.tmp ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sA_bA (src mx : Stk) (S : Scr src mx) : S.sA ≠ S.bA := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sA_bB (src mx : Stk) (S : Scr src mx) : S.sA ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_bA_bB (src mx : Stk) (S : Scr src mx) : S.bA ≠ S.bB := by
  have h := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at h
  tauto

theorem Scr.ne_sp_src (src mx : Stk) (S : Scr src mx) : S.sp ≠ src := S.ne_src S.sp (by simp)
theorem Scr.ne_sp_mx (src mx : Stk) (S : Scr src mx) : S.sp ≠ mx := S.ne_mx S.sp (by simp)

theorem Scr.ne_spc_src (src mx : Stk) (S : Scr src mx) : S.spc ≠ src := S.ne_src S.spc (by simp)
theorem Scr.ne_spc_mx (src mx : Stk) (S : Scr src mx) : S.spc ≠ mx := S.ne_mx S.spc (by simp)

theorem Scr.ne_ds_src (src mx : Stk) (S : Scr src mx) : S.ds ≠ src := S.ne_src S.ds (by simp)
theorem Scr.ne_ds_mx (src mx : Stk) (S : Scr src mx) : S.ds ≠ mx := S.ne_mx S.ds (by simp)

theorem Scr.ne_tmp_src (src mx : Stk) (S : Scr src mx) : S.tmp ≠ src := S.ne_src S.tmp (by simp)
theorem Scr.ne_tmp_mx (src mx : Stk) (S : Scr src mx) : S.tmp ≠ mx := S.ne_mx S.tmp (by simp)

theorem Scr.ne_sA_src (src mx : Stk) (S : Scr src mx) : S.sA ≠ src := S.ne_src S.sA (by simp)
theorem Scr.ne_sA_mx (src mx : Stk) (S : Scr src mx) : S.sA ≠ mx := S.ne_mx S.sA (by simp)

theorem Scr.ne_bA_src (src mx : Stk) (S : Scr src mx) : S.bA ≠ src := S.ne_src S.bA (by simp)
theorem Scr.ne_bA_mx (src mx : Stk) (S : Scr src mx) : S.bA ≠ mx := S.ne_mx S.bA (by simp)

theorem Scr.ne_bB_src (src mx : Stk) (S : Scr src mx) : S.bB ≠ src := S.ne_src S.bB (by simp)
theorem Scr.ne_bB_mx (src mx : Stk) (S : Scr src mx) : S.bB ≠ mx := S.ne_mx S.bB (by simp)


/-- The list `[S.sp, S.sA, S.bA, S.bB, mx]` is `Nodup` (the pairwise distinctness facts available for
the two branch lemmas). -/
theorem Scr.nodup5 (src mx : Stk) (S : Scr src mx) : [S.sp, S.sA, S.bA, S.bB, mx].Nodup := by
  have h7 := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or,
    List.nodup_nil, and_true] at h7
  have hsp := S.ne_sp_mx
  have hsA := S.ne_sA_mx
  have hbA := S.ne_bA_mx
  have hbB := S.ne_bB_mx
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or,
    List.nodup_nil, and_true]
  tauto

end Work.Transform.Pw
