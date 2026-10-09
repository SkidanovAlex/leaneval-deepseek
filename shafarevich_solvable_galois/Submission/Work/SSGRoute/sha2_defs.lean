import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared definitions for the `Ш²(k,M) = 0` route

* `Triv p` — `𝔽_p` with the trivial action of every group;
* `HasseUnits k` — the arithmetic core (the Hasse principle for `Br k` in the `D_A`- and
  involution-form supplied by `Z2loc`).

Kept in a separate module so that the helper files of the route can import it without importing
`Submission.Work.SSGRoute.sha2_trivial_vanish` (which is the target statement).
-/

set_option linter.ambiguousOpen false

namespace Work.SSGRoute

open scoped Pointwise

/-- `𝔽_p` as a coefficient module with the *trivial* action of every group. -/
abbrev Triv (p : ℕ) : Type := ZMod p

namespace Triv

instance (p : ℕ) : AddCommGroup (Triv p) := inferInstanceAs (AddCommGroup (ZMod p))
instance (p : ℕ) : Module (ZMod p) (Triv p) := inferInstanceAs (Module (ZMod p) (ZMod p))
instance (p : ℕ) [NeZero p] : Fintype (Triv p) := inferInstanceAs (Fintype (ZMod p))

instance (p : ℕ) (Γ : Type*) [One Γ] : SMul Γ (Triv p) where smul := fun _ x => x

instance (p : ℕ) (Γ : Type*) [Monoid Γ] : DistribMulAction Γ (Triv p) where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance (p : ℕ) (Γ : Type*) [Monoid Γ] : SMulCommClass Γ (ZMod p) (Triv p) where
  smul_comm := fun _ _ _ => rfl

end Triv

/-- **The arithmetic core**: Hasse's theorem for the Brauer group of a number field, in the form
supplied by `Z2loc`: a continuous `2`-cocycle with values in the units of an algebraic closure of a
number field which is a coboundary on the decomposition group of every finite place and on `⟨σ⟩`
for every involution `σ` is a coboundary. -/
def HasseUnits (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      Additive (AlgebraicClosure k)ˣ),
    (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) ∈
      Work.AbsoluteKummer.Z2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Additive (AlgebraicClosure k)ˣ) →
    (∀ A : ValuationSubring (AlgebraicClosure k), SSGRoute.IsFinPlace k A →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧
        ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A,
          d g h = g • b h - b (g * h) + b g) →
    (∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ ^ 2 = 1 →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (Subgroup.zpowers σ) b ∧
        ∀ g ∈ Subgroup.zpowers σ, ∀ h ∈ Subgroup.zpowers σ,
          d g h = g • b h - b (g * h) + b g) →
    (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) ∈
      Work.AbsoluteKummer.B2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Additive (AlgebraicClosure k)ˣ)

end Work.SSGRoute
