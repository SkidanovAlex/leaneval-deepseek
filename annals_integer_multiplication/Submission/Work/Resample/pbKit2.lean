import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbKit
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.dupFromEv
import Submission.Work.ConvR.sizes
import Submission.Work.Kernel.Raw

/-!
# Two-step helpers for `Work.Resample.pbWords`

* `pbScratch2` — two stacks distinct from `0`, from a given stack, and from each other;
* `pbMvValEv` — `Work.Layout.mvVal_ev_full` with the scratch stacks hidden from the frame;
* `pbCopyEv` — the `Ev`-level spec of the copy word `Work.Resample.pbCopy`
  (`Submission/Work/Resample/pbKit.lean`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- There are two stacks distinct from `0`, from `a`, and from each other. -/
theorem pbScratch2 (a : Stk) : ∃ c d : Stk, c ≠ d ∧ c ≠ 0 ∧ c ≠ a ∧ d ≠ 0 ∧ d ≠ a := by
  fin_cases a <;> decide

/-- `Work.Layout.mvVal_ev_full` with the scratch stacks hidden from the frame condition. -/
theorem pbMvValEv {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (vsz v + 1) ∧ s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  obtain ⟨s', n, hev, hn, ha', hb', hc', hd', hfr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) hab hac had hbc hbd hcd ha hb
  refine ⟨s', n, hev, hn, ha', hb', ?_⟩
  intro k hka hkb
  by_cases hkc : k = c
  · rw [hkc]; exact hc'
  · by_cases hkd : k = d
    · rw [hkd]; exact hd'
    · exact hfr k hka hkb hkc hkd

/-- `Work.Resample.pbCopy a b c d` copies the top value of stack `a` onto stack `b`, restoring
stack `a` and the scratch stacks `c`, `d`. -/
theorem pbCopyEv {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Work.Layout.Ev main (pbCopy a b c d) ⟨g, X⟩ s' n ∧ n ≤ 24 * (vsz v + 1) ∧
      s'.stk a = v.enc ++ A ∧ s'.stk b = v.enc ++ B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, hev₂, hn₂, hc₂, hb₂, ha₂, hf₂⟩ :=
    Work.Layout.drain2_ev (main := main) (c := c) (b1 := b) (b2 := a) hbc hac hab.symm
      (G := v.enc.reverse) (C := X c) (B1 := B) (B2 := A) (g := s₁.reg) (X := s₁.stk)
      (Work.Layout.gMark_not_mem_enc_rev v) hc₁ hb₁ ha₁
  have hmain : Work.Layout.Ev main (pbCopy a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold pbCopy
    exact Work.Layout.Ev.seq hev₁ hev₂
  have hnlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hn₂' : n₂ ≤ 5 * (vsz v + 1) + 2 := by rw [← hnlen]; exact hn₂
  refine ⟨s₂, _, hmain, ?_, ?_, ?_, ?_⟩
  · have h₁ : n₁ ≤ 10 * vsz v + 10 := hn₁
    have hv := Work.ConvR.vsz_one_le v
    omega
  · rw [ha₂, List.reverse_reverse]
  · rw [hb₂, List.reverse_reverse]
  · intro k hka hkb
    by_cases hkc : k = c
    · rw [hkc]; exact hc₂
    · by_cases hkd : k = d
      · rw [hkd, hf₂ d (Ne.symm hcd) hbd.symm had.symm]; exact hd₁
      · rw [hf₂ k hkc hkb hka]; exact hf₁ k hka hkc hkd

end Work.Resample

namespace Work.Resample

open HvdH

/-- A `BinOp`-style multiplier (`HvdH.IntLib`'s `mulS`) gives the natural-number multiplier word of
`Work.Resample.mulNatWord`.  The cost is multiplied by `4` because `isz (a : ℤ) = a.size + 2 ≤
2 * (a.size + 1)`. -/
theorem mulNatWord_of_binOp
    (h : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, BinOp main prog (fun _ _ => True) (· * ·)
      (fun a b => K * isz a * isz b)) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ rest : List Val,
      WordR main prog (fun vs => vs = .int (a : ℤ) :: .int (b : ℤ) :: rest)
        (fun _ out => out = .int ((a * b : ℕ) : ℤ) :: rest)
        (fun _ => K * (a.size + 1) * (b.size + 1)) := by
  obtain ⟨prog, K, hK⟩ := h
  refine ⟨prog, 4 * K, ?_⟩
  intro main a b _ _ rest vs hvs s R hR
  subst hvs
  obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ :=
    hK main _ ⟨(a : ℤ), (b : ℤ), rest, rfl, trivial⟩ s R hR
  obtain ⟨a', b', rest', heq, hout⟩ := hpost
  simp only [List.cons.injEq, Val.int.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hout]
    simp only [Nat.cast_mul]
  · have h1 : isz (a : ℤ) = a.size + 2 := by simp [isz]
    have h2 : isz (b : ℤ) = b.size + 2 := by simp [isz]
    have hc : binCost (fun a b => K * isz a * isz b)
        (.int (a : ℤ) :: .int (b : ℤ) :: rest) = K * isz (a : ℤ) * isz (b : ℤ) := rfl
    rw [hc] at hn
    have hkey : isz (a : ℤ) * isz (b : ℤ) ≤ 4 * ((a.size + 1) * (b.size + 1)) := by
      rw [h1, h2]
      nlinarith
    calc n ≤ K * isz (a : ℤ) * isz (b : ℤ) := hn
      _ = K * (isz (a : ℤ) * isz (b : ℤ)) := by ring
      _ ≤ K * (4 * ((a.size + 1) * (b.size + 1))) := Nat.mul_le_mul_left _ hkey
      _ = 4 * K * (a.size + 1) * (b.size + 1) := by ring

end Work.Resample
