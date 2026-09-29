import Mathlib
import Submission.Work.Resample.pbWords

namespace Work.Resample

open HvdH

/-- Word 6 of `Work.Resample.pbWords`, in the *framed* form: the whole stack description is
restored (`b = a`), not merely stack 2.  The program `pbProdProg mulP` copies the list `intList l`
from stack 2 to stack 7 (`pbCopy`, which restores stack 2) and folds the copy into the accumulator
on stack 0; `pbFoldEv` restores stack 7 and every other non-zero stack at the raw-glyph level, so
the description `a` is still valid at the end and can be returned as `b`. -/
theorem pbW6f :
    ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (l : List ℕ) (L acc : List HvdH.Val),
      (∀ t ∈ l, 2 ≤ t) →
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.Val.int (1 : ℤ) :: acc ∧ a 2 = HvdH.intList l :: L)
        (fun vs a out b => out = HvdH.Val.int l.prod :: acc ∧ b = a)
        (fun _ _ => Kc * (l.length + 1) *
          (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + l.prod.size + 2) * (l.prod.size + 2)) := by
  obtain ⟨mulP, Km, hmul⟩ := mulNatWord
  obtain ⟨Kf, hfold⟩ := pbFoldEv mulP Km hmul
  refine ⟨pbProdProg mulP, 200 * (Kf + 1), ?_⟩
  intro main l L acc hl
  intro vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h0acc : X 0 = (Val.int 1).enc ++ (encs acc ++ R) := by
    rw [h0X, hvs, Work.Kernel.encs_cons, List.append_assoc]
  have h2X : X 2 = (intList l).enc ++ (encs L ++ Bg 2) := by
    rw [hkX 2 (by decide), ha, Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₁, N₁, hev₁, hN₁, h2₁, h7₁, hfr₁⟩ :=
    pbCopyEv (main := main) (a := 2) (b := pbElt) (c := pbC1) (d := pbC2)
      (hab := by decide) (hac := by decide) (had := by decide) (hbc := by decide)
      (hbd := by decide) (hcd := by decide)
      (g := g) (X := X) (v := intList l) (A := encs L ++ Bg 2) (B := X pbElt) h2X rfl
  have h0₁ : s₁.stk 0 = (Val.int (1 : ℤ)).enc ++ (encs acc ++ R) := by
    rw [hfr₁ 0 (by decide) (by decide)]
    exact h0acc
  obtain ⟨s₂, N₂, hev₂, hN₂, h0₂, h7₂, hfr₂⟩ :=
    hfold main 1 (le_refl 1) l (fun t ht => by have := hl t ht; omega) acc R (X pbElt) s₁.reg
      s₁.stk h0₁ h7₁
  obtain ⟨n₁, he₁, hn₁⟩ := hev₁
  obtain ⟨n₂, he₂, hn₂⟩ := hev₂
  have hfin : Eval main (pbProdProg mulP) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold pbProdProg
    exact Eval.seq he₁ he₂
  refine ⟨Val.int l.prod :: acc, a, s₂, n₁ + n₂, ⟨rfl, rfl⟩, hfin, ?_, ?_, ?_⟩
  · exact pbW6cost Kf l n₁ n₂ N₁ N₂ hN₁ hN₂ hn₁ hn₂
  · rw [h0₂, Work.Kernel.encs_cons]
    simp only [Nat.one_mul, List.append_assoc]
  · intro k hk0
    by_cases hk2 : k = 2
    · subst hk2
      rw [hfr₂ 2 (by decide) (by decide), h2₁, ha, Work.Kernel.encs_cons]
      simp only [List.append_assoc]
    · by_cases hk7 : k = pbElt
      · subst hk7
        have h7₂' : s₂.stk pbElt = X pbElt := h7₂
        rw [h7₂']
        exact hkX pbElt (by decide)
      · rw [hfr₂ k hk0 hk7, hfr₁ k hk2 hk7, hkX k hk0]

end Work.Resample
