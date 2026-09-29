import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.dupInt_ev
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Move
import Submission.Work.Layout.merge_readFlag
import Submission.Work.Layout.merge_updSizeSkip
import Submission.Work.Layout.mrgUpdSize

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Shared tools for the proof of `Sk.mergeStep`'s specification

This module collects what the assembly of `Work.Layout.mrgMergeStep` and the individual
phase lemmas about `Sk.mergeStep` (prefix, comparison phase, the two moves) have in common:

* the cost bounds `pushSizeCost` / `updSizeCost` of the cached-size update;
* arithmetic facts showing that these costs fit into the `mrgStep` budget (`cExp`);
* two generic `Ev` tools (`Ev`-inversion of a `seq`, and composition of `seqs` lists);
* small `encs` bookkeeping lemmas.
-/

namespace Work.Layout

open HvdH Work.Layout

/-! ## the cost of the cached-size update -/

/-- cost bound for `Sk.pushSize pSize S SA t d` applied to the record `Val.cons (Val.int k) v'` -/
def pushSizeCost (KSz k : ℕ) : ℕ :=
  40 * (isz (k : ℤ) + 1) + KSz * isz (k : ℤ) + 16 * (isz (k.size : ℤ) + 1) + 8

/-- cost bound for `Sk.updSize pSize S SA t d` when `S` still carries a record
(the bound proved in `Work.Layout.mrgUpdSize`) -/
def updSizeCost (KSz k : ℕ) : ℕ := 4 + pushSizeCost KSz k

/-- the cost of `pushSize` is covered by the `cExp` term of `mrgStep` -/
theorem pushSizeCost_le_cExp (KSz k : ℕ) (v' : Val) :
    pushSizeCost KSz k ≤ cExp KSz * (vsz (Val.cons (Val.int (k : ℤ)) v') + 2) := by
  rw [pushSizeCost, cExp, vsz_record, isz_natCast, isz_ksv]
  have h := size_le_self k.size
  have hv := one_le_vsz v'
  nlinarith

/-- the cost of `updSize` (with the size update) is covered by the `cExp` term of `mrgStep` -/
theorem updSizeCost_le_cExp (KSz k : ℕ) (v' : Val) :
    updSizeCost KSz k ≤ cExp KSz * (vsz (Val.cons (Val.int (k : ℤ)) v') + 2) := by
  rw [updSizeCost, pushSizeCost, cExp, vsz_record, isz_natCast, isz_ksv]
  have h := size_le_self k.size
  have hv := one_le_vsz v'
  nlinarith

/-- when nothing is left to expose, `updSize` is the cheap `skip` -/
theorem four_le_cExp_nil (KSz : ℕ) : 4 ≤ cExp KSz * (vsz (Val.nil : Val) + 2) := by
  have h : vsz (Val.nil : Val) = 1 := rfl
  rw [cExp, h]
  nlinarith

/-! ## generic `Ev` tools -/

/-- inversion of `Ev` for a `seq` -/
theorem ev_seq_decomp {main : Cmd} {p q : Cmd} {s s' : State} {C : ℕ}
    (h : Ev main (.seq p q) s s' C) :
    ∃ s'' C₁ C₂, Ev main p s s'' C₁ ∧ Ev main q s'' s' C₂ ∧ C₁ + C₂ ≤ C := by
  obtain ⟨n, he, hn⟩ := h
  cases he with
  | seq h₁ h₂ => exact ⟨_, _, _, ⟨_, h₁, le_rfl⟩, ⟨_, h₂, le_rfl⟩, by omega⟩

/-- composing two `seqs` lists -/
theorem Ev.seqs_append {main : Cmd} {l₁ : List Cmd} :
    ∀ {l₂ : List Cmd} {s t u : State} {C₁ C₂ : ℕ}, Ev main (seqs l₁) s t C₁ →
      Ev main (seqs l₂) t u C₂ → Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  induction l₁ with
  | nil =>
      intro l₂ s t u C₁ C₂ h₁ h₂
      obtain ⟨n, he, hn⟩ := h₁
      cases he with
      | skip => simpa using h₂.mono (show C₂ ≤ C₁ + C₂ by omega)
  | cons c cs ih =>
      cases cs with
      | nil =>
          intro l₂ s t u C₁ C₂ h₁ h₂
          have h₁' : Ev main c s t C₁ := h₁
          simpa using Ev.seqs_cons (c := c) (cs := l₂) (C₁ := C₁) (C₂ := C₂) h₁' h₂
      | cons d ds =>
          intro l₂ s t u C₁ C₂ h₁ h₂
          obtain ⟨s₁, Ca, Cb, ha, hb, hab⟩ := ev_seq_decomp h₁
          have hrec := ih (l₂ := l₂) (s := s₁) (t := t) (u := u) (C₁ := Cb) (C₂ := C₂) hb h₂
          have := Ev.seqs_cons (cs := (d :: ds) ++ l₂) ha hrec
          exact this.mono (by omega)

/-! ## `encs` bookkeeping -/

/-- the encoding of a two-element list of values -/
theorem encs_two (a b : Val) (R : List Glyph) : encs [a, b] ++ R = a.enc ++ (b.enc ++ R) := by
  simp only [encs, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.nil_append, List.append_assoc]

/-- a record's encoding, with its leading `cons` glyph -/
theorem record_cons_decomp (k : ℕ) (v' : Val) (ps : List Val) (A : List Glyph) :
    (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A =
      Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))) := by
  simp only [Val.enc, List.cons_append, List.append_assoc]

/-- reassembling a record from its pieces -/
theorem record_cons_recomp (k : ℕ) (v' : Val) (ps : List Val) (A : List Glyph) :
    Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))) =
      (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
  simp only [Val.enc, List.cons_append, List.append_assoc]

/-- the head of a nonempty list of records is a record, and `keyOf` reads its key -/
theorem headD_record {l : List Val}
    (hl : ∀ v ∈ l, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'') (h : l ≠ []) :
    ∃ (k' : ℕ) (v'' : Val), l.headD Val.nil = Val.cons (Val.int (k' : ℤ)) v'' ∧
      keyOf (l.headD Val.nil) = k' := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
      obtain ⟨k', v'', hv⟩ := hl a (by simp)
      exact ⟨k', v'', by simpa using hv, by rw [show (a :: t).headD Val.nil = a from rfl, hv, keyOf_record]⟩

/-! ## the shape of `Sk.mergeStep` -/

/-- the tail of `Sk.mergeStep`: the two flag tests and the three cases -/
def mrgTail (pLt pSize : Cmd) (SX SY SA SB T F1 F2 t d : Stk) : Cmd :=
  .ite Sk.rH (Glyph.bit true)
    (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons, mvVal SY T t d,
           Sk.updSize pSize SY SB t d])
    (.ite Sk.rG (Glyph.bit true)
      (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons, mvVal SX T t d,
             Sk.updSize pSize SX SA t d])
      (seqs ([Sk.dupInt SX 0 t d, Sk.dupInt SY 0 t d, pLt, mvVal 0 F2 t d,
              Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons, pushConst SY Glyph.cons]
             ++ [.ite Sk.rG (Glyph.bit true)
                   (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d])
                   (seqs [mvVal SX T t d, Sk.updSize pSize SX SA t d])])))

/-- the 12-command prefix of `Sk.mergeStep` -/
def mrgPreL (pLt : Cmd) (SX SY SA SB F1 F2 t d : Stk) : List Cmd :=
  [.pop SX Sk.rI, .pop SY Sk.rJ, Sk.dupInt SA 0 t d, Sk.dupInt SB 0 t d, pLt,
   mvVal 0 F1 t d, Sk.dupInt SB 0 t d, Sk.dupInt SA 0 t d, pLt, mvVal 0 F2 t d,
   Sk.readFlag F1 Sk.rH, Sk.readFlag F2 Sk.rG]

/-- `Sk.mergeStep` splits into its 12-command prefix and its tail -/
theorem mergeStep_eq (pLt pSize : Cmd) (SX SY SA SB T F1 F2 t d : Stk) :
    Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d
      = seqs (mrgPreL pLt SX SY SA SB F1 F2 t d
              ++ [mrgTail pLt pSize SX SY SA SB T F1 F2 t d]) := rfl

end Work.Layout
