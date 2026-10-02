import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generators of dual rank-one modules pair to a unit

This is the algebraic core of the route to the local degree recorded in `README.md` §24, in the
form recommended by the review: the statement is made for a **variable commutative ring** `R`, so
that no `R`-specific scalar-action instance is ever selected by hand (`README.md` §21.2, §22.1).

Let `M` and `N` be `R`-modules with `M ≃ₗ[R] Hom_R(N,R)` — the situation in which
`Work.Cohomology.uctDual_evaluation` places the relative Kronecker pairing (through
`Work.Cohomology.relDualComplexIso`).  If

* `u ∈ M` is a *cyclic generator* (`Submodule.span R {u} = ⊤`), and
* `c ∈ N` carries a *primitive* functional (`φ : N →ₗ[R] R` with `φ c = 1`; for a cyclic free
  `R`-module of rank one such a `φ` is the dual basis functional),

then `f u c` is a **unit** of `R`, i.e. `f u c = ±1` when `R = ℤ`.

Applied to `M = H^{k+8}(X, X∖0)`, `N = H_{k+8}(X, X∖0)`, `u = π^*x ⌣ U` (the Thom-iso image of a
generator of `H⁸(V)`) and `c` the collapse class, this says that the local degree
`U ⌢ c = z_*[V]` holds *up to sign*: the remaining geometric inputs are only that `u` and `c` are
cyclic generators of the (free, rank-one) relative groups and that the evaluation
`H^{k+8} ≅ Hom_ℤ(H_{k+8},ℤ)` is an isomorphism.  The sign itself is an orientation normalisation and
is not decided here.
-/

namespace Work.Tubular

/-- **Generators of dual cyclic modules pair to a unit.**  If `f : M ≃ₗ[R] (N →ₗ[R] R)` is an
isomorphism of `M` with the `R`-dual of `N`, if `u` spans `M`, and if `φ` is a functional on `N`
with `φ c = 1`, then `f u c` is a unit of `R`. -/
theorem isUnit_of_linearEquiv_dual {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M ≃ₗ[R] (N →ₗ[R] R)) (u : M) (c : N) (φ : N →ₗ[R] R) (hφ : φ c = 1)
    (hu : Submodule.span R {u} = ⊤) : IsUnit (f u c) := by
  -- surjectivity of `f` produces a preimage of the primitive functional `φ`
  obtain ⟨v, hv⟩ := f.surjective φ
  -- `v` is a multiple of the generator `u`
  have hvspan : v ∈ Submodule.span R ({u} : Set M) := by rw [hu]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvspan
  -- hence `1 = φ c = a * (f u c)`, so `f u c` is a unit
  have h3 : (f v) c = a * (f u c) := by
    rw [← ha, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h1 : (1 : R) = a * (f u c) := by rw [← h3, hv, hφ]
  exact isUnit_iff_exists_inv.mpr ⟨a, by rw [mul_comm, ← h1]⟩

/-- The integral form: for `R = ℤ` the pairing of two cyclic generators of dual rank-one groups is
`1` or `-1`. -/
theorem eq_one_or_neg_one_of_linearEquiv_dual {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M ≃ₗ[ℤ] (N →ₗ[ℤ] ℤ)) (u : M) (c : N) (φ : N →ₗ[ℤ] ℤ) (hφ : φ c = 1)
    (hu : Submodule.span ℤ {u} = ⊤) : f u c = 1 ∨ f u c = -1 := by
  have h := isUnit_of_linearEquiv_dual f u c φ hφ hu
  rwa [Int.isUnit_iff] at h

end Work.Tubular
