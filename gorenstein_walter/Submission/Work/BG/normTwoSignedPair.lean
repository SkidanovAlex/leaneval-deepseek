import Mathlib
import Submission.Work.BG.CharBridge

/-!
# Area BG: norm-two virtual characters are signed pairs of irreducibles

A virtual character `φ ∈ ℤ[Irr G]` of squared norm `2` is a `ℤ`-linear combination of
exactly two distinct irreducible characters, and both coefficients are `±1`.

The proof is purely Fourier-algebraic and does not use any degree argument: writing
`φ = ∑_{a} c_a · a` with `c_a ∈ ℤ` over its support in `Irr(G)` (the layer-2 API
`mem_ZIrr_inner_self_eq_sum_sq` of the Feit–Thompson closure), Parseval turns the
hypothesis `‖φ‖² = 2` into `∑_a c_a² = 2`, and the integer-vector lemma
`exists_pair_of_sum_sq_eq_two` pins the support down to two elements with coefficients
`±1`.  (The sibling `exists_irr_sub_irr_of_inner_self_two` is the special case where the
two signs are opposite, detected there through `φ(1) = 0`; here the signs are free.)
-/

namespace Work.BG

open OddOrder.RepresentationTheory

theorem normTwoSignedPair {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {φ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hφ : φ ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hnorm : OddOrder.RepresentationTheory.ClassFunction.inner φ φ = 2) :
    ∃ (α β : OddOrder.RepresentationTheory.IrreducibleCharacter G) (ε₁ ε₂ : ℤ), α ≠ β ∧
      φ = (ε₁ : ℂ) • (α : OddOrder.RepresentationTheory.ClassFunction G ℂ) +
          (ε₂ : ℂ) • (β : OddOrder.RepresentationTheory.ClassFunction G ℂ) := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 2 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, β₀, hαβ, hs, _hcα, _hcβ⟩ := exists_pair_of_sum_sq_eq_two hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβ₀ : β₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  refine ⟨⟨α₀, hα₀⟩, ⟨β₀, hβ₀⟩, c α₀, c β₀, fun h => hαβ (congrArg Subtype.val h), ?_⟩
  rw [hrepr, hs, Finset.sum_pair hαβ]

end Work.BG
