import Mathlib
import Submission.Work.BG.normTwoSignedPair
import Submission.Work.BG.CharBridge
import Submission.Work.BG.inner_pmIrr_eq_pm_one

namespace Work.BG

open OddOrder.RepresentationTheory Work.BG

/-- A `±1`-multiple of an irreducible character is a signed irreducible character
(`IsPmIrr`): either the coefficient is `1` and the class function *is* irreducible, or it is
`-1` and the negation of the class function is irreducible. -/
private lemma isPmIrr_smul_of_isIrreducible {K : Type} [Group K]
    {α : ClassFunction K ℂ} {ε : ℤ}
    (hα : IsIrreducibleCharacter α) (hε : ε = 1 ∨ ε = -1) :
    IsPmIrr ((ε : ℂ) • α) := by
  rcases hε with rfl | rfl
  · left; simpa using hα
  · right; simpa using hα

/-- Two distinct irreducible characters are orthogonal. -/
private lemma inner_eq_zero_of_ne_of_isIrreducible {K : Type} [Group K] [Finite K]
    [Fintype K] [Invertible (Nat.card K : ℂ)]
    {α β : ClassFunction K ℂ} (hα : IsIrreducibleCharacter α)
    (hβ : IsIrreducibleCharacter β) (hαβ : α ≠ β) :
    ClassFunction.inner α β = 0 := by
  have h := irreducibleCharacter_inner_eq_ite (⟨α, hα⟩ : IrreducibleCharacter K) ⟨β, hβ⟩
  rw [ite_eq_right] at h
  · exact h
  · intro hh; exact hαβ (congrArg Subtype.val hh)

/-- Scalar multiples of orthogonal class functions are orthogonal. -/
private lemma inner_smul_smul_eq_zero {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {α β : ClassFunction K ℂ} {ε₁ ε₂ : ℤ}
    (h : ClassFunction.inner α β = 0) :
    ClassFunction.inner ((ε₁ : ℂ) • α) ((ε₂ : ℂ) • β) = 0 := by
  rw [ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, h, mul_zero, mul_zero]

open OddOrder.RepresentationTheory Work.BG in
theorem c3NormTwoPair {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ : ClassFunction K ℂ}
    (hφ : φ ∈ ZIrr K) (hnorm : ClassFunction.inner φ φ = 2) :
    ∃ χ₁ χ₂ : ClassFunction K ℂ, IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧
      ClassFunction.inner χ₁ χ₂ = 0 ∧ φ = χ₁ + χ₂ := by
  obtain ⟨α, β, εα, εβ, hα, hβ, hαβ, hεα, hεβ, hφeq⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hφ hnorm
  have horth : ClassFunction.inner α β = 0 :=
    inner_eq_zero_of_ne_of_isIrreducible hα hβ hαβ
  exact ⟨(εα : ℂ) • α, (εβ : ℂ) • β,
    isPmIrr_smul_of_isIrreducible hα hεα,
    isPmIrr_smul_of_isIrreducible hβ hεβ,
    inner_smul_smul_eq_zero horth,
    hφeq⟩

end Work.BG
