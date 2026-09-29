import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.Kernel

open HvdH

/-! ## Helpers: only `Val.nil` encodes to something starting with `Glyph.nil` -/

theorem ifNil_headD_nil (v : HvdH.Val) (hv : v = HvdH.Val.nil) (rest : List HvdH.Val)
    (R : List HvdH.Glyph) :
    (HvdH.encs (v :: rest) ++ R).headD HvdH.Glyph.eos = HvdH.Glyph.nil := by
  subst hv; simp [Work.Kernel.encs_cons, HvdH.Val.enc]

theorem ifNil_headD_ne (v : HvdH.Val) (hv : v ≠ HvdH.Val.nil) (rest : List HvdH.Val)
    (R : List HvdH.Glyph) :
    (HvdH.encs (v :: rest) ++ R).headD HvdH.Glyph.eos ≠ HvdH.Glyph.nil := by
  rw [Work.Kernel.encs_cons]; cases v with
  | int z => simp only [HvdH.Val.enc]; split <;> simp
  | nil => exact absurd rfl hv
  | cons a b => simp [HvdH.Val.enc]

/-- Tails of the encoding stack: removing the `nil` encoding exposes `rest`. -/
theorem ifNil_tail_encs_nil (rest : List HvdH.Val) (R : List HvdH.Glyph) :
    (HvdH.encs (HvdH.Val.nil :: rest) ++ R).tail = HvdH.encs rest ++ R := by
  simp [Work.Kernel.encs_cons, HvdH.Val.enc]

/-! ## Helpers: the canonical states of `peek`/`pop` at stack `0` -/

theorem ifNil_tPeek_reg (s : HvdH.State) :
    (HvdH.State.tPeek s 0 0).reg 0 = (s.stk 0).headD HvdH.Glyph.eos := by
  simp [HvdH.State.tPeek, HvdH.State.updReg]

theorem ifNil_tPeek_stk0 (s : HvdH.State) : (HvdH.State.tPeek s 0 0).stk 0 = s.stk 0 := by
  simp [HvdH.State.tPeek]

theorem ifNil_tPeek_stk (s : HvdH.State) (k : HvdH.Stk) :
    (HvdH.State.tPeek s 0 0).stk k = s.stk k := by
  simp [HvdH.State.tPeek]

theorem ifNil_tPop_stk0 (s : HvdH.State) :
    (HvdH.State.tPop s 0 0).stk 0 = (s.stk 0).tail := by
  simp [HvdH.State.tPop]

theorem ifNil_tPop_stk (s : HvdH.State) {k : HvdH.Stk} (hk : k ≠ 0) :
    (HvdH.State.tPop s 0 0).stk k = s.stk k := by
  simp [HvdH.State.tPop, HvdH.State.updStk_apply, hk]

/-- `import Submission.Work.Kernel.Raw`, work in `namespace Work.Kernel`.  `HvdH.Val.enc (.nil) = [Glyph.nil]` is the only encoding starting with `Glyph.nil`.  Helpers in this file must be named with the prefix `ifNil_`. -/
theorem ifNil : ∃ (comb : HvdH.Cmd → HvdH.Cmd → HvdH.Cmd) (K : ℕ), ∀ (main q₁ q₂ : HvdH.Cmd) (v : HvdH.Val) (rest : List HvdH.Val)
    (Q₁ Q₂ : List HvdH.Val → Prop) (c₁ c₂ : ℕ),
    (v = HvdH.Val.nil → HvdH.WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
    (v ≠ HvdH.Val.nil → HvdH.WordR main q₂ (fun vs => vs = v :: rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
    HvdH.WordR main (comb q₁ q₂) (fun vs => vs = v :: rest)
      (fun _ out => (v = HvdH.Val.nil → Q₁ out) ∧ (v ≠ HvdH.Val.nil → Q₂ out)) (fun _ => K + max c₁ c₂) := by
  refine ⟨fun q₁ q₂ => HvdH.Cmd.seq (HvdH.Cmd.peek 0 0)
      (HvdH.Cmd.ite 0 HvdH.Glyph.nil (HvdH.Cmd.seq (HvdH.Cmd.pop 0 0) q₁) q₂), 3, ?_⟩
  intro main q₁ q₂ v rest Q₁ Q₂ c₁ c₂ h₁ h₂ vs hvs s R hR
  subst hvs
  by_cases hv : v = HvdH.Val.nil
  · -- the top value is `nil`: pop its (single-glyph) encoding and run `q₁`
    have hhead : (HvdH.State.tPeek s 0 0).reg 0 = HvdH.Glyph.nil := by
      rw [ifNil_tPeek_reg, hR]; exact ifNil_headD_nil v hv rest R
    have hs2 : (HvdH.State.tPop (HvdH.State.tPeek s 0 0) 0 0).stk 0 = HvdH.encs rest ++ R := by
      rw [ifNil_tPop_stk0, ifNil_tPeek_stk0, hR, hv]
      exact ifNil_tail_encs_nil rest R
    obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
      h₁ hv rest rfl (HvdH.State.tPop (HvdH.State.tPeek s 0 0) 0 0) R hs2
    refine ⟨out, s', 1 + ((1 + n) + 1), ⟨fun _ => hQ, fun hne => absurd hv hne⟩, ?_, ?_, hstk, ?_⟩
    · exact eval_seq (eval_peek main 0 0 s)
        (eval_iteT hhead (eval_seq (eval_pop main 0 0 (HvdH.State.tPeek s 0 0)) he))
    · have hn' : n ≤ c₁ := hn
      have hmax : c₁ ≤ max c₁ c₂ := Nat.le_max_left _ _
      show 1 + ((1 + n) + 1) ≤ 3 + max c₁ c₂
      omega
    · intro k hk
      rw [hoth k hk, ifNil_tPop_stk (HvdH.State.tPeek s 0 0) hk, ifNil_tPeek_stk s k]
  · -- the top value is not `nil`: keep it and run `q₂`
    have hhead : (HvdH.State.tPeek s 0 0).reg 0 ≠ HvdH.Glyph.nil := by
      rw [ifNil_tPeek_reg, hR]; exact ifNil_headD_ne v hv rest R
    have hs1 : (HvdH.State.tPeek s 0 0).stk 0 = HvdH.encs (v :: rest) ++ R := by
      rw [ifNil_tPeek_stk0]; exact hR
    obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
      h₂ hv (v :: rest) rfl (HvdH.State.tPeek s 0 0) R hs1
    refine ⟨out, s', 1 + (n + 1), ⟨fun heq => absurd heq hv, fun _ => hQ⟩, ?_, ?_, hstk, ?_⟩
    · exact eval_seq (eval_peek main 0 0 s) (eval_iteF hhead he)
    · have hn' : n ≤ c₂ := hn
      have hmax : c₂ ≤ max c₁ c₂ := Nat.le_max_right _ _
      show 1 + (n + 1) ≤ 3 + max c₁ c₂
      omega
    · intro k hk
      rw [hoth k hk, ifNil_tPeek_stk s k]

end Work.Kernel
