import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.BSW.Cases.Order

open OddOrder.RepresentationTheory

theorem shareOfInnerEqNegOne {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {α β ψ₁ ψ₂ ν₁ ν₂ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hψ₁ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ₁)
    (hψ₂ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ₂)
    (hν₁ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν₁)
    (hν₂ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν₂)
    (hψ : ψ₁ ≠ ψ₂) (hν : ν₁ ≠ ν₂)
    (hα : α = OddOrder.RepresentationTheory.trivialClassFunction G + ψ₁ - ψ₂)
    (hβ : β = ν₁ - ν₂)
    (hneu : OddOrder.RepresentationTheory.ClassFunction.inner β
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0)
    (hAB : OddOrder.RepresentationTheory.ClassFunction.inner α β = -1) :
    ψ₁ = ν₂ ∨ ψ₂ = ν₁ := by
  classical
  -- orthonormality of irreducible characters, for unbundled class functions
  have inner_irr : ∀ {φ ψ : ClassFunction G ℂ}, IsIrreducibleCharacter φ →
      IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφ⟩ : IrreducibleCharacter G)
      (⟨ψ, hψ⟩ : IrreducibleCharacter G)
    simpa only [IrreducibleCharacter.coe_mk, Subtype.mk.injEq] using h
  -- the trivial-character term drops out
  have htriv : ClassFunction.inner (trivialClassFunction G) β = 0 := by
    rw [ClassFunction.inner_star_comm, hneu, star_zero]
  have hαval : ClassFunction.inner α β = ClassFunction.inner (ψ₁ - ψ₂) β := by
    rw [hα, show trivialClassFunction G + ψ₁ - ψ₂
        = trivialClassFunction G + (ψ₁ - ψ₂) from by abel,
      ClassFunction.inner_add_left, htriv, zero_add]
  have hmain : ClassFunction.inner (ψ₁ - ψ₂) β = -1 := by
    rw [← hαval]; exact hAB
  rw [hβ] at hmain
  have hexpand : ClassFunction.inner (ψ₁ - ψ₂) (ν₁ - ν₂)
      = ClassFunction.inner ψ₁ ν₁ - ClassFunction.inner ψ₁ ν₂
        - ClassFunction.inner ψ₂ ν₁ + ClassFunction.inner ψ₂ ν₂ := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    ring
  rw [hexpand] at hmain
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hB : ClassFunction.inner ψ₁ ν₂ = 0 := by
    rw [inner_irr hψ₁ hν₂, if_neg h1]
  have hC : ClassFunction.inner ψ₂ ν₁ = 0 := by
    rw [inner_irr hψ₂ hν₁, if_neg h2]
  have hA : ClassFunction.inner ψ₁ ν₁ = 1 ∨ ClassFunction.inner ψ₁ ν₁ = 0 := by
    rw [inner_irr hψ₁ hν₁]; by_cases h : ψ₁ = ν₁ <;> simp [h]
  have hD : ClassFunction.inner ψ₂ ν₂ = 1 ∨ ClassFunction.inner ψ₂ ν₂ = 0 := by
    rw [inner_irr hψ₂ hν₂]; by_cases h : ψ₂ = ν₂ <;> simp [h]
  rw [hB, hC] at hmain
  rcases hA with hA | hA <;> rcases hD with hD | hD <;>
    rw [hA, hD] at hmain <;> norm_num at hmain

end Work.BSW.Cases.Order
