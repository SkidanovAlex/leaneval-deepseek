import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.Kernel

open HvdH

/-- Arithmetic core of the induction step of `dropValueLoopLe`: if one body run costs `c₀ ≤ c` and
an `n`-fold unrolled loop costs at most `n * (c + 1) + 1`, then the `(n+1)`-fold unrolled loop costs
at most `(n + 1) * (c + 1) + 1` at its exact cost `c₀ + m' + 1`. -/
theorem loopCostStep (c c₀ m' n : ℕ) (h₁ : c₀ ≤ c) (h₂ : m' ≤ n * (c + 1) + 1) :
    c₀ + m' + 1 ≤ (n + 1) * (c + 1) + 1 := by
  have h : c + (n * (c + 1) + 1) + 1 = (n + 1) * (c + 1) + 1 := by ring
  omega

/-- `Cmd.loop` unrolled along an explicit sequence of states, with only a *bound* `c` on each body run (generalises `Work.Kernel.eval_loop_iterate` in `Submission/Work/Kernel/Raw.lean`, where each body run must cost exactly `c`; `Eval` costs are exact, so padding is not available in general). -/
theorem dropValueLoopLe (main : HvdH.Cmd) (r : HvdH.Reg) (cc : HvdH.Glyph) (body : HvdH.Cmd) (c : ℕ) :
    ∀ (n : ℕ) (f : ℕ → HvdH.State),
      (∀ i < n, (f i).reg r = cc ∧ ∃ c' ≤ c, HvdH.Eval main body (f i) (f (i + 1)) c') →
      (f n).reg r ≠ cc →
      ∃ m ≤ n * (c + 1) + 1, HvdH.Eval main (HvdH.Cmd.loop r cc body) (f 0) (f n) m := by
  intro n
  induction n with
  | zero =>
    intro f _ hstop
    exact ⟨1, by simp, Eval.loopF (main := main) (s := f 0) hstop⟩
  | succ n ih =>
    intro f hstep hstop
    obtain ⟨h0reg, c₀, hc₀, h0ev⟩ := hstep 0 (Nat.zero_lt_succ n)
    obtain ⟨m', hm', hloop⟩ :=
      ih (fun i => f (i + 1)) (fun i hi => hstep (i + 1) (by omega)) hstop
    exact ⟨c₀ + m' + 1, loopCostStep c c₀ m' n hc₀ hm', Eval.loopT h0reg h0ev hloop⟩

end Work.Kernel
