import Mathlib
import Submission.Work.BG.deltaShape
import Submission.Work.BG.L41Aux
import Submission.Work.BG.ThmABCCharDefs

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Fourier bookkeeping.** If all Fourier coefficients of `δ` against irreducible characters
are `±1` or `0`, then `⟨χ, δ⟩ ∈ {0, 1, -1}` for every signed irreducible character `χ`
(as a genuine integer, not merely as a complex number).

Both orientations of the inner product occur, so we use `inner_star_comm`; the value is a
real integer, so `star` is invisible. -/
private lemma inner_pmIrr_eq_zero_or_pm_one {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {δ χ : ClassFunction K ℂ} (hχ : IsPmIrr χ)
    (hint : ∀ ξ : IrreducibleCharacter K,
      ClassFunction.inner δ (ξ : ClassFunction K ℂ) = 1 ∨
        ClassFunction.inner δ (ξ : ClassFunction K ℂ) = -1 ∨
        ClassFunction.inner δ (ξ : ClassFunction K ℂ) = 0) :
    ∃ m : ℤ, (m = 0 ∨ m = 1 ∨ m = -1) ∧ ClassFunction.inner χ δ = (m : ℂ) := by
  rcases hχ with hirr | hneg
  · have h' : ClassFunction.inner δ χ = 1 ∨ ClassFunction.inner δ χ = -1 ∨
        ClassFunction.inner δ χ = 0 := by
      have h := hint ⟨χ, hirr⟩
      simpa only [IrreducibleCharacter.coe_mk] using h
    rcases h' with h | h | h
    · exact ⟨1, Or.inr (Or.inl rfl), by
        rw [ClassFunction.inner_star_comm, h]; simp⟩
    · exact ⟨-1, Or.inr (Or.inr rfl), by
        rw [ClassFunction.inner_star_comm, h]; simp⟩
    · exact ⟨0, Or.inl rfl, by
        rw [ClassFunction.inner_star_comm, h]; simp⟩
  · have h' : ClassFunction.inner δ (-χ) = 1 ∨ ClassFunction.inner δ (-χ) = -1 ∨
        ClassFunction.inner δ (-χ) = 0 := by
      have h := hint ⟨-χ, hneg⟩
      simpa only [IrreducibleCharacter.coe_mk] using h
    -- `χ = -(-χ)`, so `⟨χ, δ⟩ = -⟨-χ, δ⟩`; conjugate symmetry restores `⟨χ, δ⟩`.
    rcases h' with h | h | h
    · refine ⟨-1, Or.inr (Or.inr rfl), ?_⟩
      rw [show χ = -(-χ) from (neg_neg χ).symm, ClassFunction.inner_neg_left,
        ClassFunction.inner_star_comm, h]
      simp
    · refine ⟨1, Or.inr (Or.inl rfl), ?_⟩
      rw [show χ = -(-χ) from (neg_neg χ).symm, ClassFunction.inner_neg_left,
        ClassFunction.inner_star_comm, h]
      simp
    · refine ⟨0, Or.inl rfl, ?_⟩
      rw [show χ = -(-χ) from (neg_neg χ).symm, ClassFunction.inner_neg_left,
        ClassFunction.inner_star_comm, h]
      simp

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem l41iiiDelta {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) {β₂ : Work.BG.quotGroup C.P →* ℂˣ}
    (hβ₂ : β₂ ≠ 1) {χ : ClassFunction G ℂ} (hχ : Work.BG.IsPmIrr χ)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.S4Index C) :
    ∃ m : ℤ, (m = 0 ∨ m = 1 ∨ m = -1) ∧
      ClassFunction.inner χ (Work.GW2.C16.delta C β₂ ν) = (m : ℂ) := by
  obtain ⟨T, _hTcard, hTin, hTout⟩ := deltaShape D C hc hn β₂ hβ₂ ν hν
  refine inner_pmIrr_eq_zero_or_pm_one hχ fun ξ => ?_
  by_cases hmem : ξ ∈ T
  · rcases hTin ξ hmem with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hTout ξ hmem))

end Work.BG
