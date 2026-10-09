import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class form of the §4 conclusion

`ZSix` is the six-conjunct form of Schmidt–Wingberg's auxiliary class `z` (arXiv:math/9809211, §4,
`A = μ_p`): the conclusion of `Work.SSGRoute.sw_z_exists_odd_sketch` and of
`Work.SSGRoute.ZDataMup.swZExistsOddSketchH`.  It is the *class form* of the node
`Work.SSGRoute.H9.sw_odd_kummer_core_proved`, from which the Kummer form follows through the Kummer
correspondence (`Work.SSGRoute.H9.sw_odd_kummer_core_of_zSix`).
-/

open scoped Pointwise

namespace Work.SSGRoute.H9

open _root_.SSGRoute

/-- **The class form of the §4 conclusion** (Schmidt–Wingberg's auxiliary class `z`): additive and
locally constant on `G_K`, agreeing with `y` on the local groups of the classes of `S`, vanishing on
the involutions, killing the inertia of the places outside the classes of `S` that are not split in
`N`, and killing the local groups of the `k`-conjugates (that are not `K`-conjugates) of the places
outside the classes of `S` split in `N` at which it is ramified. -/
def ZSix (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
    IsLocConstOn K.fixingSubgroup z ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → z σ = y σ) ∧
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z σ = 0) ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k N B →
      (∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
        ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, z τ = 0)

end Work.SSGRoute.H9
