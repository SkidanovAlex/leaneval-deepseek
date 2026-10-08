import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Char.inner_alpha_beta
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.BSW.Cases.Order

open OddOrder.RepresentationTheory

/-- A virtual character `φ ∈ ZIrr G` with `⟨φ, φ⟩ = 2`, `⟨φ, 1_G⟩ = 0` and `φ(1) = 0` is the
difference `ν₁ - ν₂` of two distinct irreducible characters of equal degree.

Mathematically: Parseval gives `Σ_χ n_χ² = 2` with `n_χ ∈ ℤ`, so exactly two irreducible
characters occur, each with coefficient `±1`; since the signs must be opposite (`φ(1) = 0`
with positive degrees), `φ` is the difference of two distinct irreducibles, and evaluating at
`1` gives `ν₁(1) = ν₂(1)`.  (`⟨φ, 1_G⟩ = 0` is not needed for the conclusion.) -/
theorem existsDecompTwo {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hZ : φ ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hnorm : OddOrder.RepresentationTheory.ClassFunction.inner φ φ = 2)
    (hone : OddOrder.RepresentationTheory.ClassFunction.inner φ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0) (h0 : φ 1 = 0) :
    ∃ ν₁ ν₂ : OddOrder.RepresentationTheory.ClassFunction G ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ν₁ ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ν₂ ∧ ν₁ ≠ ν₂ ∧
      φ = ν₁ - ν₂ ∧ ν₂ 1 = ν₁ 1 := by
  classical
  obtain ⟨α, β, hαβ, hdecomp⟩ := exists_irr_sub_irr_of_inner_self_two hZ hnorm h0
  refine ⟨(α : ClassFunction G ℂ), (β : ClassFunction G ℂ), α.isIrreducible, β.isIrreducible,
    fun h => hαβ (IrreducibleCharacter.ext h), hdecomp, ?_⟩
  have h : (α : ClassFunction G ℂ) 1 - (β : ClassFunction G ℂ) 1 = 0 := by
    have h := h0
    rw [hdecomp] at h
    simpa using h
  exact (sub_eq_zero.mp h).symm

end Work.BSW.Cases.Order
