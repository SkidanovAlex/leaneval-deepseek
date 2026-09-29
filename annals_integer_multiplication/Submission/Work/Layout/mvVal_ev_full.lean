import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

namespace Work.Layout

/-- Full-strength `mvVal`: like `Work.Layout.mvVal_ev`, but additionally records that the scratch
stacks `c` and `d` are restored exactly. -/
theorem mvVal_ev_full {main : HvdH.Cmd} {a b c d : HvdH.Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {v : HvdH.Val} {A B : List HvdH.Glyph}
    (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz v + 1) ∧ s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧
      s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : HvdH.Stk, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    mvB_ev (main := main) hbc (G := v.enc.reverse) (C := X c) (B := B)
      (gMark_not_mem_enc_rev v) hc₁ hb₁
  have hlen : (v.enc.reverse).length = HvdH.vsz v := by simp [HvdH.vsz]
  have hn₂' : n₂ ≤ 4 * (HvdH.vsz v + 1) + 3 := by
    rw [← hlen]; exact hn₂
  have hmain : Ev main (mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold mvVal
    exact Ev.seq h1 h2
  have hcost : n₁ + n₂ ≤ 16 * (HvdH.vsz v + 1) := by
    have h₁ : n₁ ≤ 10 * HvdH.vsz v + 10 := hn₁
    have h₂ : n₂ ≤ 4 * (HvdH.vsz v + 1) + 3 := hn₂'
    have hv := one_le_vsz v
    omega
  refine ⟨s₂, _, hmain, hcost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ a hac hab]; exact ha₁
  · rw [hb₂, List.reverse_reverse]
  · rw [hc₂]
  · rw [hf₂ d hcd.symm hbd.symm]; exact hd₁
  · intro k hka hkb hkc hkd
    rw [hf₂ k hkc hkb]
    exact hf₁ k hka hkc hkd

end Work.Layout
