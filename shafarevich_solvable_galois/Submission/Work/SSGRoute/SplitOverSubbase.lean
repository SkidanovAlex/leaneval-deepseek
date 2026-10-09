import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Complete decomposition measured over a sub-base `k₀ ≤ k`

`SSGRoute.IsSplitIn k N B` measures complete decomposition of the place `B` in the level field `N`
over the base field `k`: it is the subgroup containment `decomp k B ≤ N.fixingSubgroup`
(equivalently, every `k`-automorphism of `Ω` stabilising `B` fixes `N` pointwise).

For the Fourth Step of Schmidt--Wingberg the notion has to be measured over a **sub-base**
`k₀ ≤ k` (in the application `k = ↥K` and `k₀ = ℚ`): the level field `N` is not assumed Galois over
`k₀`, so the correct (and the only available) formalisation is the pointwise one:

  `B` is completely decomposed in `N` **over `k₀`**  ⟺  every `σ ∈ Ω ≃ₐ[k₀] Ω` stabilising `B`
  fixes `N` pointwise.

This is the predicate `IsSplitOverSub` below.  Note

* `decomp k B ⊆ decomp k₀ B` (`decomp_le_decomp_subbase`), hence
* `IsSplitOverSub ⟹ IsSplitIn k N B` (`isSplitIn_of_isSplitOverSub`), i.e. the sub-base condition is
  the *stronger* one: the places it singles out are exactly the places at which the `k`-level escape
  clause of `SSGRoute.coker_obstruction` is too weak.

Nothing in this file is `sorry`.
-/

open scoped Pointwise

namespace SSGRoute

section Subbase

variable (k₀ : Type) [Field k₀] (k : Type) [Field k] (Ω : Type) [Field Ω]
  [Algebra k₀ k] [Algebra k₀ Ω] [Algebra k Ω] [IsScalarTower k₀ k Ω]

/-- `B` is a finite place of `Ω` which is completely decomposed in the level field `N` **over the
sub-base `k₀`**: every `k₀`-automorphism of `Ω` stabilising `B` fixes `N` pointwise. -/
def IsSplitOverSub (N : IntermediateField k Ω) (B : ValuationSubring Ω) : Prop :=
  ∀ σ : Ω ≃ₐ[k₀] Ω, σ ∈ decomp k₀ B → ∀ x ∈ (N : Set Ω), σ x = x

/-- The pointwise action on `ValuationSubring Ω` only depends on the underlying map, so restricting
scalars from `k` to `k₀ ≤ k` does not change it. -/
theorem restrictScalars_smul_subbase (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) :
    AlgEquiv.restrictScalars k₀ σ • B = σ • B := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [AlgEquiv.smul_def]
  rw [show ((AlgEquiv.restrictScalars k₀ σ)⁻¹ : Ω ≃ₐ[k₀] Ω) x = (σ⁻¹ : Ω ≃ₐ[k] Ω) x from rfl]

/-- Every `k`-automorphism of `Ω` is a `k₀`-automorphism (`k₀ ≤ k`), so the `k`-decomposition group
of a place is contained in its `k₀`-decomposition group. -/
theorem decomp_le_decomp_subbase (B : ValuationSubring Ω) :
    ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ decomp k B → AlgEquiv.restrictScalars k₀ σ ∈ decomp k₀ B := by
  intro σ hσ
  rw [decomp, MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [restrictScalars_smul_subbase k₀ k Ω B σ, hσ]

/-- `IsSplitOverSub` is the spelled-out pointwise condition. -/
theorem isSplitOverSub_iff (N : IntermediateField k Ω) (B : ValuationSubring Ω) :
    IsSplitOverSub k₀ k Ω N B ↔
      ∀ σ : Ω ≃ₐ[k₀] Ω, σ ∈ decomp k₀ B → ∀ x ∈ (N : Set Ω), σ x = x := Iff.rfl

/-- The sub-base notion of complete decomposition is the stronger one: if `B` is completely
decomposed in `N` over `k₀`, then it is split in `N` over `k` in the sense of
`SSGRoute.IsSplitIn`. -/
theorem isSplitIn_of_isSplitOverSub (N : IntermediateField k Ω) (B : ValuationSubring Ω)
    (h : IsSplitOverSub k₀ k Ω N B) : IsSplitIn k N B := by
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact h (AlgEquiv.restrictScalars k₀ σ) (decomp_le_decomp_subbase k₀ k Ω B σ hσ)

end Subbase

end SSGRoute
