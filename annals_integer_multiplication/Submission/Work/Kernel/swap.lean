import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Kernel.dropValue

namespace Work.Kernel

open HvdH

/-- `swap_prog`: move the top value `a` of stack 0 to the scratch stack 1, then the value `b`
below it to the scratch stack 2; then move stack 1 back on top of stack 0 (giving `a :: rest`) and
finally stack 2 on top of that (giving `b :: a :: rest`).  Stacks 3 and 4 are the buffer/counter of
the `mvVal` movers; all four scratch stacks (`1`,`2`,`3`,`4`) are restored. -/
def swap_prog : HvdH.Cmd :=
  Work.Layout.seqs [Work.Layout.mvVal 0 1 3 4, Work.Layout.mvVal 0 2 3 4,
    Work.Layout.mvVal 1 0 3 4, Work.Layout.mvVal 2 0 3 4]

/-- `swap_prog` swaps the top two values of stack 0 at cost `≤ 64 * (vsz a + vsz b + 1)`: it is a
chain of four `mvVal` movers, each of cost `≤ 16 * (vsz v + 1)`. -/
theorem swap_prog_wordR : ∀ main : HvdH.Cmd, HvdH.WordR main swap_prog (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (fun vs => 64 * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1)) := by
  intro main vs hvs s R hR
  cases vs with
  | nil => simp at hvs
  | cons a vs' =>
    cases vs' with
    | nil => simp at hvs
    | cons b rest =>
      have h0 : s.stk 0 = a.enc ++ (b.enc ++ (encs rest ++ R)) := by
        rw [hR, encs_cons, encs_cons]
        simp only [List.append_assoc]
      -- step 1: move `a` from stack 0 to stack 1
      obtain ⟨s₁, n₁, hE₁, hn₁, h0₁, h1₁, h3₁, h4₁, hf₁⟩ :=
        Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 3) (d := 4)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (g := s.reg) (X := s.stk) (v := a) (A := b.enc ++ (encs rest ++ R)) (B := s.stk 1)
          h0 rfl
      -- step 2: move `b` from stack 0 to stack 2
      obtain ⟨s₂, n₂, hE₂, hn₂, h0₂, h2₂, h3₂, h4₂, hf₂⟩ :=
        Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 2) (c := 3) (d := 4)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (g := s₁.reg) (X := s₁.stk) (v := b) (A := encs rest ++ R) (B := s₁.stk 2) h0₁ rfl
      -- step 3: move `a` back on top of stack 0
      have h1₂ : s₂.stk 1 = a.enc ++ s.stk 1 := by
        rw [hf₂ 1 (by decide) (by decide) (by decide) (by decide), h1₁]
      obtain ⟨s₃, n₃, hE₃, hn₃, h1₃, h0₃, h3₃, h4₃, hf₃⟩ :=
        Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 3) (d := 4)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (g := s₂.reg) (X := s₂.stk) (v := a) (A := s.stk 1) (B := s₂.stk 0) h1₂ rfl
      -- step 4: move `b` on top of stack 0
      have h2₃ : s₃.stk 2 = b.enc ++ s.stk 2 := by
        rw [hf₃ 2 (by decide) (by decide) (by decide) (by decide), h2₂,
          hf₁ 2 (by decide) (by decide) (by decide) (by decide)]
      obtain ⟨s₄, n₄, hE₄, hn₄, h2₄, h0₄, h3₄, h4₄, hf₄⟩ :=
        Work.Layout.mvVal_ev_full (main := main) (a := 2) (b := 0) (c := 3) (d := 4)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (g := s₃.reg) (X := s₃.stk) (v := b) (A := s.stk 2) (B := s₃.stk 0) h2₃ rfl
      obtain ⟨m₁, he₁, hm₁⟩ := hE₁
      obtain ⟨m₂, he₂, hm₂⟩ := hE₂
      obtain ⟨m₃, he₃, hm₃⟩ := hE₃
      obtain ⟨m₄, he₄, hm₄⟩ := hE₄
      have hE : Eval main (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 3 4)
          (HvdH.Cmd.seq (Work.Layout.mvVal 0 2 3 4)
            (HvdH.Cmd.seq (Work.Layout.mvVal 1 0 3 4) (Work.Layout.mvVal 2 0 3 4))))
          ⟨s.reg, s.stk⟩ s₄ (m₁ + (m₂ + (m₃ + m₄))) :=
        Eval.seq he₁ (Eval.seq he₂ (Eval.seq he₃ he₄))
      refine ⟨b :: a :: rest, s₄, m₁ + (m₂ + (m₃ + m₄)), ⟨a, b, rest, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simpa [swap_prog, Work.Layout.seqs] using hE
      · simp only [List.getD_cons_zero, List.getD_cons_succ]
        omega
      · rw [h0₄, h0₃, h0₂]
        simp only [encs_cons, List.append_assoc]
      · intro k hk
        by_cases hk1 : k = 1
        · subst hk1
          rw [hf₄ 1 (by decide) (by decide) (by decide) (by decide)]
          exact h1₃
        · by_cases hk2 : k = 2
          · subst hk2
            exact h2₄
          · by_cases hk3 : k = 3
            · subst hk3
              rw [h3₄, h3₃, h3₂]
              exact h3₁
            · by_cases hk4 : k = 4
              · subst hk4
                rw [h4₄, h4₃, h4₂]
                exact h4₁
              · rw [hf₄ k hk2 hk hk3 hk4, hf₃ k hk1 hk hk3 hk4, hf₂ k hk hk2 hk3 hk4,
                  hf₁ k hk hk1 hk3 hk4]

/-- `swap` field of `HvdH.KernelLib` (v2/v3). -/
theorem swap : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ main : HvdH.Cmd, HvdH.WordR main prog (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (fun vs => K * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1)) :=
  ⟨swap_prog, 64, swap_prog_wordR⟩

end Work.Kernel
