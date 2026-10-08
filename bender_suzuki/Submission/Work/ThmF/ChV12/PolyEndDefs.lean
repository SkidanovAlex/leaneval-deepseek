import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The polynomial action `ℤ[σ]` on an additive commutative group

For an additive commutative group `M` and an additive automorphism `σ : M ≃+ M`, the polynomial
ring `ℤ[X]` acts on `M` through `X ↦ σ`: the element `p = ∑ cᵢ Xⁱ` acts by
`x ↦ ∑ cᵢ • σⁱ x`.  This is the ring hom `polyEnd σ : ℤ[X] →+* End M` studied here.  It makes
`M` a module over the commutative ring `ℤ[σ]`, and the `σ`-invariant additive subgroups of `M`
are exactly its `ℤ[X]`-submodules.

This file collects the elementary API of `polyEnd`, used both by
`Submission.Work.ThmF.ChV12.mulAut_mul_comm_of_commute_of_irreducible` and by the auxiliary
lemmas about it.
-/

namespace Work.ThmF.ChV12

/-- The unital ring hom `ℤ[X] →+* End M` sending `X` to `σ`.  Equivalently `p ↦ p(σ)`. -/
noncomputable abbrev polyEnd {M : Type*} [AddCommGroup M] (σ : M ≃+ M) :
    Polynomial ℤ →+* AddMonoid.End M :=
  (Polynomial.aeval (A := AddMonoid.End M) σ.toAddMonoidHom).toRingHom

/-- `polyEnd σ` sends `X` to `σ`. -/
theorem polyEnd_X {M : Type*} [AddCommGroup M] (σ : M ≃+ M) :
    polyEnd σ Polynomial.X = σ.toAddMonoidHom :=
  Polynomial.aeval_X (A := AddMonoid.End M) σ.toAddMonoidHom

/-- `X` acts as `σ`. -/
@[simp]
theorem polyEnd_X_apply {M : Type*} [AddCommGroup M] (σ : M ≃+ M) (x : M) :
    polyEnd σ Polynomial.X x = σ x := by
  rw [polyEnd_X]; rfl

/-- `1` acts as the identity. -/
@[simp]
theorem polyEnd_one_apply {M : Type*} [AddCommGroup M] (σ : M ≃+ M) (x : M) :
    polyEnd σ (1 : Polynomial ℤ) x = x := by
  rw [show polyEnd σ (1 : Polynomial ℤ) = 1 from map_one (polyEnd σ)]; rfl

/-- The action is multiplicative in the polynomial. -/
theorem polyEnd_mul_apply {M : Type*} [AddCommGroup M] (σ : M ≃+ M)
    (p q : Polynomial ℤ) (x : M) :
    polyEnd σ (p * q) x = polyEnd σ p (polyEnd σ q x) := by
  rw [map_mul]; rfl

/-- `σ` commutes with the action of every polynomial (here written with `X` on the left). -/
theorem polyEnd_X_mul_apply {M : Type*} [AddCommGroup M] (σ : M ≃+ M)
    (p : Polynomial ℤ) (x : M) :
    σ (polyEnd σ p x) = polyEnd σ (Polynomial.X * p) x := by
  have hσ : ⇑(polyEnd σ Polynomial.X) = ⇑σ := by rw [polyEnd_X]; rfl
  calc σ (polyEnd σ p x)
      = (polyEnd σ Polynomial.X) (polyEnd σ p x) := by rw [hσ]
    _ = ((polyEnd σ Polynomial.X) * (polyEnd σ p)) x := rfl
    _ = (polyEnd σ (Polynomial.X * p)) x := by rw [map_mul]
    _ = polyEnd σ (Polynomial.X * p) x := rfl

/-- `σ` commutes with the action of every polynomial (here written with `X` on the right). -/
theorem polyEnd_mul_X_apply {M : Type*} [AddCommGroup M] (σ : M ≃+ M)
    (p : Polynomial ℤ) (x : M) :
    σ (polyEnd σ p x) = polyEnd σ (p * Polynomial.X) x := by
  rw [polyEnd_X_mul_apply, mul_comm]

/-- Applying `polyEnd σ p` after `polyEnd σ q` is applying `polyEnd σ q` after `polyEnd σ p`:
the action is by the commutative ring `ℤ[σ]`. -/
theorem polyEnd_apply_comm {M : Type*} [AddCommGroup M] (σ : M ≃+ M)
    (p q : Polynomial ℤ) (x : M) :
    polyEnd σ p (polyEnd σ q x) = polyEnd σ q (polyEnd σ p x) := by
  rw [← polyEnd_mul_apply, ← polyEnd_mul_apply, mul_comm]

end Work.ThmF.ChV12
