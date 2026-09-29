import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.Kernel

open HvdH

/-- The word of `consV`: set a scratch register to `Glyph.cons` and push it onto stack 0. -/
def consV_prog : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.set 0 Glyph.cons) (HvdH.Cmd.push 0 0)

/-- Result state of `consV_prog`. -/
def consV_state (s : HvdH.State) : HvdH.State :=
  HvdH.State.tPush (HvdH.State.tSet s 0 Glyph.cons) 0 0

theorem consV_eval (main : HvdH.Cmd) (s : HvdH.State) :
    HvdH.Eval main consV_prog s (consV_state s) 2 :=
  HvdH.Eval.seq (HvdH.Eval.set 0 Glyph.cons s) (HvdH.Eval.push 0 0 (HvdH.State.tSet s 0 Glyph.cons))

/-- `consV_prog` pushes exactly one glyph, `Glyph.cons`, on stack 0. -/
theorem consV_state_stk0 (s : HvdH.State) :
    (consV_state s).stk 0 = Glyph.cons :: s.stk 0 := by
  simp [consV_state, HvdH.State.tPush, HvdH.State.tSet, HvdH.State.updStk, HvdH.State.updReg]

/-- All other stacks are untouched. -/
theorem consV_state_stk_ne (s : HvdH.State) (k : HvdH.Stk) (hk : k ≠ 0) :
    (consV_state s).stk k = s.stk k := by
  simp [consV_state, HvdH.State.tPush, HvdH.State.tSet, HvdH.State.updStk, HvdH.State.updReg, hk]

/-- The pushed `Glyph.cons` is exactly the leading glyph of `Val.cons a b`. -/
theorem consV_stk0_eq (a b : HvdH.Val) (rest : List HvdH.Val) (R : List Glyph) :
    Glyph.cons :: (HvdH.encs (a :: b :: rest) ++ R) =
      HvdH.encs (HvdH.Val.cons a b :: rest) ++ R := by
  simp [encs_cons, HvdH.Val.enc, List.cons_append, List.append_assoc]

/-- A value stack of length at least `2` splits off its first two values. -/
theorem consV_split {vs : List HvdH.Val} (h : 2 ≤ vs.length) :
    ∃ a b rest, vs = a :: b :: rest := by
  match vs with
  | [] => simp at h
  | [_] => simp at h
  | x :: y :: ys => exact ⟨x, y, ys, rfl⟩

/-- `import Submission.Work.Kernel.Raw`, work in `namespace Work.Kernel`.  `HvdH.WordR` is the frame-carrying Hoare triple of `Submission/HvdH/Interfaces.lean`.  The program pushes the single glyph `Glyph.cons`.  Helpers in this file must be named with the prefix `consV_` (the shared namespace is flat). -/
theorem consV : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ main : HvdH.Cmd, HvdH.WordR main prog (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = HvdH.Val.cons a b :: rest) (fun _ => K) := by
  refine ⟨consV_prog, 2, ?_⟩
  intro main vs hlen s R hR
  obtain ⟨a, b, rest, rfl⟩ := consV_split hlen
  refine ⟨HvdH.Val.cons a b :: rest, consV_state s, 2, ⟨a, b, rest, rfl, rfl⟩, consV_eval main s,
    le_rfl, ?_, ?_⟩
  · rw [consV_state_stk0, hR]
    exact consV_stk0_eq a b rest R
  · intro k hk
    exact consV_state_stk_ne s k hk

end Work.Kernel
