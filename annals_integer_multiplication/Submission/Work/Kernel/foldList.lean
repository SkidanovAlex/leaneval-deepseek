import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.foldListDefs
import Submission.Work.Kernel.foldList_phase1
import Submission.Work.Kernel.foldList_phase2
import Submission.Work.Kernel.foldList_phase3

namespace Work.Kernel

open HvdH
open Work.Layout

/-- `foldList` field of `HvdH.KernelLib` (v2/v3).  Imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend`, plus the already-proved marker movers `Submission.Work.Layout.Move` (`Work.Layout.Ev` = bounded `Eval`; `mvVal_ev` moves one value between two stacks at cost `≤ 16*(vsz v+1)`).  Key encodings: `encs (ofList xs :: acc) = cons :: (encs xs ++ acc)`, `encs (x :: xs') = x.enc ++ encs xs'`, `ofList [] = .nil`.  Plan: if the top value is `nil` (i.e. `xs = []`), drop it and stop — the value stack is then `acc`, and `I 0 acc` is exactly the given precondition (this is what makes the bound `K` work at `xs = []`).  Otherwise move the elements aside one at a time (marker before each, using the pending counter as in `Submission/Work/Kernel/dropValue*.lean`); then for `i = 0, …, xs.length-1` move the next element back on top of the current accumulator stack (so `q` sees exactly `xs.getD i .nil :: acc`) and run `q` via its `WordR` hypothesis (which gives `I (i+1)`); finally discard the list markers and restore the scratch stacks.  Helpers must be named with the prefix `foldList_`. -/
theorem foldList : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ), ∀ (main q : HvdH.Cmd) (xs : List HvdH.Val)
    (I : ℕ → List HvdH.Val → Prop) (c L : ℕ),
    (∀ x ∈ xs, HvdH.vsz x ≤ L) →
    (∀ i acc, i < xs.length → I i acc → HvdH.WordR main q (fun vs => vs = xs.getD i HvdH.Val.nil :: acc)
      (fun _ out => I (i + 1) out) (fun _ => c)) →
    HvdH.WordR main (comb q) (fun vs => ∃ acc, vs = HvdH.ofList xs :: acc ∧ I 0 acc)
      (fun _ out => I xs.length out) (fun _ => xs.length * (c + K * (L + 1)) + K) := by
  refine ⟨foldList_comb, 256, ?_⟩
  intro main q xs I c L hL hq vs hvs s R hR
  obtain ⟨acc, rfl, hI⟩ := hvs
  -- phase 0: push the frame marker `foldList_tag` on both scratch stacks `1` and `2`
  obtain ⟨s₁, n₁, hE₁, hn₁, hk₁, hf₁, -, -⟩ :=
    pushConst_ev (main := main) (k := (1 : Stk)) (cst := foldList_tag) (g := s.reg) (X := s.stk)
  obtain ⟨s₂, n₂, hE₂, hn₂, hk₂, hf₂, -, -⟩ :=
    pushConst_ev (main := main) (k := (2 : Stk)) (cst := foldList_tag) (g := s₁.reg) (X := s₁.stk)
  have hs0₂ : s₂.stk 0 = encs (ofList xs :: acc) ++ R := by
    rw [hf₂ 0 (by decide), hf₁ 0 (by decide)]; exact hR
  have hs1₂ : s₂.stk 1 = foldList_tag :: s.stk 1 := by
    rw [hf₂ 1 (by decide), hk₁]
  -- phase 1: dismantle the list onto stack `1`
  obtain ⟨s₃, hE₃, hk₃₀, hk₃₁, hf₃⟩ := foldList_phase1 main xs acc R (s.stk 1) s₂ L hL hs0₂ hs1₂
  -- phase 2: move the elements to stack `2`, restoring their order
  have hs2₃ : s₃.stk 2 = foldList_tag :: s.stk 2 := by
    rw [hf₃ 2 (by decide) (by decide), hk₂, hf₁ 2 (by decide)]
  obtain ⟨s₄, hE₄, hk₄₀, hk₄₁, hk₄₂, hf₄⟩ :=
    foldList_phase2 main xs (s.stk 1) (s.stk 2) s₃ L hL hk₃₁ hs2₃
  -- phase 3: fold `q` over the elements
  have hs0₄ : s₄.stk 0 = encs acc ++ R := by rw [hk₄₀, hk₃₀]
  obtain ⟨s₅, hE₅, hk₅, hk₅₂, hf₅⟩ :=
    foldList_phase3 main q xs I acc R (s.stk 2) s₄ c L hL hq hs0₄ hI hk₄₂
  -- the whole program
  have hEv : Ev main (foldList_comb q) s s₅
      (2 + (2 + ((xs.length * (16 * (L + 1) + 4) + 4) +
        ((xs.length * (16 * (L + 1) + 5) + 5) + (xs.length * (16 * (L + 1) + c + 5) + 5))))) := by
    have hE₁' : Ev main (pushConst (1 : Stk) foldList_tag) s s₁ 2 := hE₁.mono hn₁
    have hE₂' : Ev main (pushConst (2 : Stk) foldList_tag) s₁ s₂ 2 := hE₂.mono hn₂
    have hc := Ev.seq hE₁' (Ev.seq hE₂' (Ev.seq hE₃ (Ev.seq hE₄ hE₅)))
    simpa [foldList_comb, Work.Layout.seqs] using hc
  obtain ⟨n, hEval, hn⟩ := hEv
  obtain ⟨a, hIa, hk₅₀⟩ := hk₅
  refine ⟨a, s₅, n, hIa, hEval, ?_, hk₅₀, ?_⟩
  · have hsum : 2 + (2 + ((xs.length * (16 * (L + 1) + 4) + 4) +
        ((xs.length * (16 * (L + 1) + 5) + 5) + (xs.length * (16 * (L + 1) + c + 5) + 5))))
        = xs.length * (48 * (L + 1) + c + 14) + 18 := by ring
    have hn' : n ≤ xs.length * (48 * (L + 1) + c + 14) + 18 := hsum ▸ hn
    refine le_trans hn' ?_
    have hkey : 48 * (L + 1) + c + 14 ≤ c + 256 * (L + 1) := by omega
    exact Nat.add_le_add (Nat.mul_le_mul_left xs.length hkey) (by norm_num)
  · intro k hk0
    by_cases hk2 : k = 2
    · subst hk2; exact hk₅₂
    · rw [hf₅ k hk0 hk2]
      by_cases hk1 : k = 1
      · subst hk1; exact hk₄₁
      · rw [hf₄ k hk0 hk1 hk2, hf₃ k hk0 hk1, hf₂ k hk2, hf₁ k hk1]

end Work.Kernel
