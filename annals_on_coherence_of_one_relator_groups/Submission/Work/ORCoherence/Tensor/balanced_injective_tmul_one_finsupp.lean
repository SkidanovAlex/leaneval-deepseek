import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

/-- For an injective ring homomorphism `f : R →+* S`, the map `x ↦ 1 ⊗ x` from
`X →₀ R` (with its left `R`-module structure) into the balanced tensor product
`S ⊗[R] (X →₀ R)` is injective. Indeed, evaluating the `a`-th coefficient after
applying the `S`-linear universal map `Balanced.lift` to `f ∘ ev_a` recovers `f (x a)`. -/
theorem balanced_injective_tmul_one_finsupp {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (X : Type*) :
    Function.Injective (fun x : X →₀ R => Balanced.tmul f 1 x) := by
  intro x y hxy
  ext a
  apply hf
  -- The `ℤ`-linear map `φ : (X →₀ R) → S`, `m ↦ f (m a)`, is compatible with the `R`-action.
  let φ : (X →₀ R) →ₗ[ℤ] S := (f.toIntAlgHom : R →ₗ[ℤ] S).comp
    ((Finsupp.lapply (M := R) a : (X →₀ R) →ₗ[R] R).restrictScalars ℤ)
  have hφ : ∀ (r : R) (m : X →₀ R), f r • φ m = φ (r • m) := by
    intro r m
    show f r * f (m a) = f ((r • m) a)
    rw [Finsupp.smul_apply, smul_eq_mul, map_mul]
  have key := congrArg (Balanced.lift f φ hφ) hxy
  rw [Balanced.lift_tmul_one, Balanced.lift_tmul_one] at key
  show f (x a) = f (y a)
  exact key

end Work.ORCoherence.Tensor
