import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Layout.dupFromEv
import Submission.Work.Layout.mvVal_ev_full

namespace Work.Kernel

open HvdH

/-- `dup_prog` duplicates the top value of stack 0 as `v :: v :: rest`: it moves `v` from stack 0
to the scratch stack 1, copies it back from stack 1 onto stack 0 (`Work.Layout.dupFrom 1`, which
leaves stack 1 unchanged), and finally moves the original (still on stack 1) back on top of stack 0.
Stacks `2, 3` are the buffer/counter of `mvVal` and `5, 6` those of `dupFrom`; all are restored. -/
def dup_prog : HvdH.Cmd :=
  Work.Layout.seqs [Work.Layout.mvVal 0 1 2 3, Work.Layout.dupFrom 1, Work.Layout.mvVal 1 0 2 3]

/-- `dup_prog` duplicates the top value of stack 0 at cost `≤ 48 * (vsz v + 1)`: three movers of
cost `≤ 16 * (vsz v + 1)` each. -/
theorem dup_prog_wordR : ∀ main : HvdH.Cmd, HvdH.WordR main dup_prog (fun vs => vs ≠ [])
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
    (fun vs => 48 * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) := by
  intro main vs hvs s R hR
  cases vs with
  | nil => exact absurd rfl hvs
  | cons v rest =>
    have h0 : s.stk 0 = v.enc ++ (HvdH.encs rest ++ R) := by
      rw [hR, Work.Kernel.encs_cons, List.append_assoc]
    -- step 1: move `v` from stack 0 to stack 1
    obtain ⟨s₁, n₁, hE₁, hn₁, h0₁, h1₁, h2₁, h3₁, hf₁⟩ :=
      Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (g := s.reg) (X := s.stk) (v := v) (A := HvdH.encs rest ++ R) (B := s.stk 1) h0 rfl
    -- step 2: copy `v` from stack 1 back onto stack 0 (stack 1 keeps its `v`)
    obtain ⟨s₂, n₂, hE₂, hn₂, h0₂, h1₂, hf₂⟩ :=
      Work.Layout.dupFromEv (main := main) (a := 1) (by decide) (by decide) (by decide)
        v (s.stk 1) (HvdH.encs rest ++ R) s₁.reg s₁.stk h1₁ h0₁
    -- step 3: move the original `v` from stack 1 on top of stack 0
    obtain ⟨s₃, n₃, hE₃, hn₃, h1₃, h0₃, h2₃, h3₃, hf₃⟩ :=
      Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (g := s₂.reg) (X := s₂.stk) (v := v) (A := s.stk 1)
        (B := v.enc ++ (HvdH.encs rest ++ R)) h1₂ h0₂
    obtain ⟨m₁, he₁, hm₁⟩ := hE₁
    obtain ⟨m₂, he₂, hm₂⟩ := hE₂
    obtain ⟨m₃, he₃, hm₃⟩ := hE₃
    refine ⟨v :: v :: rest, s₃, m₁ + (m₂ + m₃), ⟨v, rest, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · have hE : Eval main (Work.Layout.mvVal 0 1 2 3 ;; (Work.Layout.dupFrom 1 ;;
          Work.Layout.mvVal 1 0 2 3)) ⟨s.reg, s.stk⟩ s₃ (m₁ + (m₂ + m₃)) :=
        Eval.seq he₁ (Eval.seq he₂ he₃)
      simpa [dup_prog, Work.Layout.seqs] using hE
    · have h₁ : m₁ ≤ 16 * (vsz v + 1) := le_trans hm₁ hn₁
      have h₂ : m₂ ≤ 16 * (vsz v + 1) := le_trans hm₂ hn₂
      have h₃ : m₃ ≤ 16 * (vsz v + 1) := le_trans hm₃ hn₃
      simp only [List.headD_cons]
      omega
    · rw [h0₃, Work.Kernel.encs_cons, Work.Kernel.encs_cons, List.append_assoc,
        List.append_assoc]
    · intro k hk
      by_cases hk1 : k = 1
      · rw [hk1]; exact h1₃
      · by_cases hk2 : k = 2
        · rw [hk2, h2₃, hf₂ 2 (by decide) (by decide), h2₁]
        · by_cases hk3 : k = 3
          · rw [hk3, h3₃, hf₂ 3 (by decide) (by decide), h3₁]
          · rw [hf₃ k hk1 hk hk2 hk3, hf₂ k hk hk1, hf₁ k hk hk1 hk2 hk3]

/-- `dup` field of `HvdH.KernelLib` (v2/v3 — the interface is now true; do NOT use `Submission/Work/Kernel/loopRefute.lean`).  Useful imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend` (pending-subtree counter: `pendFold_enc`, `pendFold_take_pos`), and the *already proved* marker movers `Submission.Work.Layout.Move`: `Work.Layout.Ev main p s s' C := ∃ n, Eval main p s s' n ∧ n ≤ C` (a bounded `Eval`), and `Work.Layout.Move.mvVal_ev` moves one value from stack `a` to stack `b` (normal order) at cost `≤ 16 * (vsz v + 1)`, touching only `a, b, c, d`; `mvA_ev`/`mvB_ev` are the two halves.  Using those saves hours.  Plan: move the top value `v` of stack 0 to a scratch stack, then copy it back while writing each glyph twice, or `mvVal` it out/in as needed; the scratch stacks must be restored.  Helpers must be named with the prefix `dup_`. -/
theorem dup : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ main : HvdH.Cmd, HvdH.WordR main prog (fun vs => vs ≠ [])
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
    (fun vs => K * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) :=
  ⟨dup_prog, 48, dup_prog_wordR⟩

end Work.Kernel
