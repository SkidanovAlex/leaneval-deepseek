import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

open scoped Classical in
/-- Expanding the inner product of a two-term combination `a • α + b • β` of irreducible
characters against an irreducible character `χ`, using `ℂ`-bilinearity of the inner product
and the orthonormality `⟨χ, ψ⟩ = δ_{χψ}` of irreducible characters. -/
theorem signedPairCoeffNeZero_expand {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (a b : ℤ) {α β : ClassFunction G ℂ}
    (hα : α ∈ irreducibleCharacters G) (hβ : β ∈ irreducibleCharacters G)
    (χ : IrreducibleCharacter G) :
    ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β) (χ : ClassFunction G ℂ) =
      (a : ℂ) * (if (⟨α, hα⟩ : IrreducibleCharacter G) = χ then 1 else 0) +
      (b : ℂ) * (if (⟨β, hβ⟩ : IrreducibleCharacter G) = χ then 1 else 0) := by
  have hαχ : ClassFunction.inner α (χ : ClassFunction G ℂ) =
      if (⟨α, hα⟩ : IrreducibleCharacter G) = χ then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite ⟨α, hα⟩ χ
  have hβχ : ClassFunction.inner β (χ : ClassFunction G ℂ) =
      if (⟨β, hβ⟩ : IrreducibleCharacter G) = χ then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite ⟨β, hβ⟩ χ
  rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hαχ, hβχ]

theorem signedPairCoeffNeZero {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b : ℤ} {α β : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hα : α ∈ OddOrder.RepresentationTheory.irreducibleCharacters G)
    (hβ : β ∈ OddOrder.RepresentationTheory.irreducibleCharacters G) (hαβ : α ≠ β)
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (h : OddOrder.RepresentationTheory.ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β)
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) ≠ 0) :
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) = α ∨
      (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) = β := by
  have _ := hαβ
  have key := signedPairCoeffNeZero_expand a b hα hβ χ
  rw [key] at h
  by_cases hαχ : (⟨α, hα⟩ : IrreducibleCharacter G) = χ
  · exact Or.inl (congrArg (fun x : IrreducibleCharacter G => (x : ClassFunction G ℂ)) hαχ).symm
  by_cases hβχ : (⟨β, hβ⟩ : IrreducibleCharacter G) = χ
  · exact Or.inr (congrArg (fun x : IrreducibleCharacter G => (x : ClassFunction G ℂ)) hβχ).symm
  · exfalso
    rw [ite_eq_right hαχ, ite_eq_right hβχ] at h
    simp at h

end Work.BG
