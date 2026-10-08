import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.indexTwoMackey

namespace Work.BG

open OddOrder.RepresentationTheory

theorem indexTwoInduceEqIff {H : Type*} [Group H] [Finite H] [Fintype H] (H0 : Subgroup H)
    [H0.Normal] (hind : H0.index = 2) (s : H) (hs : s ∉ H0)
    [Invertible (Nat.card H0 : ℂ)] [Invertible (Nat.card H : ℂ)]
    (ν μ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H0) :
    OddOrder.RepresentationTheory.ClassFunction.induce H0
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) =
      OddOrder.RepresentationTheory.ClassFunction.induce H0
        (μ : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) ↔
      (μ : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) =
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) ∨
        (μ : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) =
          OddOrder.RepresentationTheory.ClassFunction.conjBy s
            (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) := by
  -- The general Clifford fibre description of induction: `Ind ν = Ind μ` iff `μ` is an
  -- `H`-conjugate of `ν` (`OddOrder.RepresentationTheory.induce_eq_induce_iff_conj`).
  have key := OddOrder.RepresentationTheory.induce_eq_induce_iff_conj (G := H) (H := H0) ν μ
  rw [key]
  constructor
  · rintro ⟨g, hg⟩
    -- `H` is the union of the two cosets of `H₀`: `g ∈ H₀` or `g ∉ H₀`.
    by_cases hgH0 : g ∈ H0
    · -- `g ∈ H₀` conjugates `ν` to itself, so `μ = ν`.
      left
      rw [← hg, IrreducibleCharacter.coe_conjBy]
      exact ClassFunction.conjBy_eq_self_of_mem (H := H0) hgH0 (ν : ClassFunction ↥H0 ℂ)
    · -- `g ∉ H₀` puts `g` in the coset `s · H₀`: `s⁻¹ * g ∈ H₀`, so `conjBy g` and
      -- `conjBy s` agree on `ν`.
      right
      rw [← hg, IrreducibleCharacter.coe_conjBy]
      have ht : s⁻¹ * g ∈ H0 := by
        rw [Subgroup.mul_mem_iff_of_index_two hind]
        constructor
        · intro h; exact absurd (show s ∈ H0 from by simpa using H0.inv_mem h) hs
        · intro h; exact absurd h hgH0
      rw [show g = s * (s⁻¹ * g) from (mul_inv_cancel_left s g).symm, ClassFunction.conjBy_mul]
      exact ClassFunction.conjBy_eq_self_of_mem (H := H0) ht _
  · rintro (h | h)
    · -- `μ = ν`: take the trivial conjugate.
      exact ⟨1, IrreducibleCharacter.ext (by rw [IrreducibleCharacter.conjBy_one]; exact h.symm)⟩
    · -- `μ = ν^s`: take the witness `s`.
      exact ⟨s, IrreducibleCharacter.ext (by rw [IrreducibleCharacter.coe_conjBy]; exact h.symm)⟩

end Work.BG
