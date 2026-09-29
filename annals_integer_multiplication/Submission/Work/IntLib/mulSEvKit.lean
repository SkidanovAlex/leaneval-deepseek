import Mathlib
import Submission.HvdH.Interfaces

/-!
# Self-contained bounded-evaluation toolkit for the multiplication word

`Ev main p s s' C` = "`p` runs from `s` to `s'` in at most `C` steps".  Everything here is proved
directly from `HvdH.Eval`; nothing outside `Submission.HvdH.Interfaces` is imported, so this module
is immune to churn in other areas' files.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace MulS

open HvdH

/-- state extensionality -/
theorem State.ext' {s t : State} (h1 : s.reg = t.reg) (h2 : s.stk = t.stk) : s = t := by
  cases s with
  | mk r X => cases t with
    | mk r' X' => simp_all

/-- `Ev main p s s' C`: `p` runs from `s` to `s'` in at most `C` steps. -/
def Ev (main : Cmd) (p : Cmd) (s s' : State) (C : ℕ) : Prop := ∃ n, Eval main p s s' n ∧ n ≤ C

theorem Ev.mono {main : Cmd} {p : Cmd} {s s' : State} {C C' : ℕ} (h : Ev main p s s' C)
    (hC : C ≤ C') : Ev main p s s' C' := by obtain ⟨n, he, hl⟩ := h; exact ⟨n, he, le_trans hl hC⟩

/-- transport an `Ev` claim along an equality of result states -/
theorem Ev.rw {main : Cmd} {p : Cmd} {s s' t' : State} {C : ℕ} (h : Ev main p s s' C)
    (hst : s' = t') : Ev main p s t' C := hst ▸ h

theorem Ev.seq {main : Cmd} {p q : Cmd} {s t u : State} {C₁ C₂ : ℕ}
    (h₁ : Ev main p s t C₁) (h₂ : Ev main q t u C₂) : Ev main (.seq p q) s u (C₁ + C₂) := by
  obtain ⟨n₁, e₁, l₁⟩ := h₁
  obtain ⟨n₂, e₂, l₂⟩ := h₂
  exact ⟨n₁ + n₂, Eval.seq e₁ e₂, by omega⟩

theorem Ev.seq' {main : Cmd} {p q : Cmd} {s t u : State} {C₁ C₂ C : ℕ}
    (h₁ : Ev main p s t C₁) (h₂ : Ev main q t u C₂) (hC : C₁ + C₂ ≤ C) :
    Ev main (.seq p q) s u C := (Ev.seq h₁ h₂).mono hC

theorem ev_skip (main : Cmd) (s : State) : Ev main .skip s s 1 := ⟨1, Eval.skip s, le_rfl⟩

theorem ev_pop (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.pop k r) s ⟨Function.update s.reg r ((s.stk k).headD .eos),
      Function.update s.stk k (s.stk k).tail⟩ 1 := ⟨1, Eval.pop k r s, le_rfl⟩

theorem ev_peek (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.peek k r) s ⟨Function.update s.reg r ((s.stk k).headD .eos), s.stk⟩ 1 :=
  ⟨1, Eval.peek k r s, le_rfl⟩

theorem ev_push (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.push k r) s ⟨s.reg, Function.update s.stk k (s.reg r :: s.stk k)⟩ 1 :=
  ⟨1, Eval.push k r s, le_rfl⟩

theorem ev_set (main : Cmd) (r : Reg) (c : Glyph) (s : State) :
    Ev main (.set r c) s ⟨Function.update s.reg r c, s.stk⟩ 1 := ⟨1, Eval.set r c s, le_rfl⟩

theorem ev_mov (main : Cmd) (dst src : Reg) (s : State) :
    Ev main (.mov dst src) s ⟨Function.update s.reg dst (s.reg src), s.stk⟩ 1 :=
  ⟨1, Eval.mov dst src s, le_rfl⟩

theorem Ev.iteT {main : Cmd} {r : Reg} {c : Glyph} {p q : Cmd} {s s' : State} {C : ℕ}
    (hr : s.reg r = c) (h : Ev main p s s' C) : Ev main (.ite r c p q) s s' (C + 1) := by
  obtain ⟨n, he, hl⟩ := h
  exact ⟨n + 1, Eval.iteT hr he, by omega⟩

theorem Ev.iteF {main : Cmd} {r : Reg} {c : Glyph} {p q : Cmd} {s s' : State} {C : ℕ}
    (hr : s.reg r ≠ c) (h : Ev main q s s' C) : Ev main (.ite r c p q) s s' (C + 1) := by
  obtain ⟨n, he, hl⟩ := h
  exact ⟨n + 1, Eval.iteF hr he, by omega⟩

theorem Ev.loopF {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s : State}
    (hr : s.reg r ≠ c) : Ev main (.loop r c body) s s 1 := ⟨1, Eval.loopF hr, le_rfl⟩

theorem Ev.loopT {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s s' s'' : State} {C₁ C₂ : ℕ}
    (hr : s.reg r = c) (h₁ : Ev main body s s' C₁) (h₂ : Ev main (.loop r c body) s' s'' C₂) :
    Ev main (.loop r c body) s s'' (C₁ + C₂ + 1) := by
  obtain ⟨n₁, e₁, l₁⟩ := h₁
  obtain ⟨n₂, e₂, l₂⟩ := h₂
  exact ⟨n₁ + n₂ + 1, Eval.loopT hr e₁ e₂, by omega⟩

/-! ## Frame: stacks a program never touches -/

/-- The set of stacks a program may touch.  `self` may touch anything. -/
def cmdTouches : Cmd → Finset Stk
  | .skip => ∅
  | .pop k _ => {k}
  | .peek k _ => {k}
  | .push k _ => {k}
  | .set _ _ => ∅
  | .mov _ _ => ∅
  | .seq a b => cmdTouches a ∪ cmdTouches b
  | .ite _ _ a b => cmdTouches a ∪ cmdTouches b
  | .loop _ _ a => cmdTouches a
  | .self => Finset.univ

theorem Eval.stk_frame {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n)
    {k : Stk} (hk : k ∉ cmdTouches c) : s'.stk k = s.stk k := by
  induction h with
  | skip s => rfl
  | pop k' r s =>
      simp only [cmdTouches, Finset.mem_singleton] at hk
      show Function.update s.stk k' (s.stk k').tail k = s.stk k
      exact Function.update_of_ne hk _ _
  | peek k' r s => rfl
  | push k' r s =>
      simp only [cmdTouches, Finset.mem_singleton] at hk
      show Function.update s.stk k' (s.reg r :: s.stk k') k = s.stk k
      exact Function.update_of_ne hk _ _
  | set r c s => rfl
  | mov dst src s => rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      simp only [cmdTouches, Finset.mem_union, not_or] at hk
      rw [ih₂ hk.2, ih₁ hk.1]
  | iteT hr h ih =>
      simp only [cmdTouches, Finset.mem_union, not_or] at hk
      exact ih hk.1
  | iteF hr h ih =>
      simp only [cmdTouches, Finset.mem_union, not_or] at hk
      exact ih hk.2
  | loopF hr => rfl
  | loopT hr h₁ h₂ ih₁ ih₂ =>
      simp only [cmdTouches] at hk
      rw [ih₂ hk, ih₁ hk]
  | self h ih => exact absurd (Finset.mem_univ _) hk

theorem Ev.frame {main : Cmd} {p : Cmd} {s s' : State} {C : ℕ} (h : Ev main p s s' C)
    {S : Finset Stk} (hS : cmdTouches p ⊆ S) {k : Stk} (hk : k ∉ S) : s'.stk k = s.stk k := by
  obtain ⟨n, he, _⟩ := h
  exact Eval.stk_frame he fun hc => hk (hS hc)

/-! ## Program lists -/

/-- Sequence a list of commands (no trailing `skip`). -/
def seqs : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## `loopRuns`: a fixed number of loop iterations -/

/-- `loopRuns main rf c body k s s' C`: starting from `s`, the body of `loop rf c body` runs
`k` times (each time the test `reg rf = c` succeeds), reaching `s'`, total cost `≤ C`. -/
def loopRuns (main : Cmd) (rf : Reg) (c : Glyph) (body : Cmd) : ℕ → State → State → ℕ → Prop
  | 0, s, s', C => s' = s ∧ C = 0
  | k + 1, s, s', C => s.reg rf = c ∧
      ∃ s₁ C₁ C₂, Ev main body s s₁ C₁ ∧ loopRuns main rf c body k s₁ s' C₂ ∧ C₁ + C₂ + 1 ≤ C

theorem loopRuns.eval {main : Cmd} {rf : Reg} {c : Glyph} {body : Cmd} :
    ∀ {k : ℕ} {s s' : State} {C : ℕ}, loopRuns main rf c body k s s' C → s'.reg rf ≠ c →
      Ev main (.loop rf c body) s s' (C + 1) := by
  intro k
  induction k with
  | zero =>
      intro s s' C h hne
      obtain ⟨hs, hC⟩ := h
      subst hs; subst hC
      exact ⟨1, Eval.loopF hne, by omega⟩
  | succ k ih =>
      intro s s' C h hne
      obtain ⟨hrf, s₁, C₁, C₂, hb, hr, hle⟩ := h
      obtain ⟨n₁, e₁, l₁⟩ := hb
      obtain ⟨n₂, e₂, l₂⟩ := ih hr hne
      exact ⟨n₁ + n₂ + 1, Eval.loopT hrf e₁ e₂, by omega⟩

theorem loopRuns.zero {main : Cmd} {rf : Reg} {c : Glyph} {body : Cmd} {s : State} :
    loopRuns main rf c body 0 s s 0 := ⟨rfl, rfl⟩

theorem loopRuns.succ' {main : Cmd} {rf : Reg} {c : Glyph} {body : Cmd} {k : ℕ} {s s₁ s' : State}
    {C₁ C₂ C : ℕ} (hr : s.reg rf = c) (hb : Ev main body s s₁ C₁)
    (hr' : loopRuns main rf c body k s₁ s' C₂) (hle : C₁ + C₂ + 1 ≤ C) :
    loopRuns main rf c body (k + 1) s s' C := ⟨hr, s₁, C₁, C₂, hb, hr', hle⟩

end MulS
end Work.IntLib
