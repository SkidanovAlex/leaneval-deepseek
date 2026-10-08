import Mathlib
import Submission.Work.ThmF.ChV12.Gl2Cyclic.minpoly_irreducible_of_no_eigen

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12.Gl2Cyclic

open Polynomial

/-- **The group of polynomials in `x` is cyclic.**

Let `V` be a finite-dimensional vector space over a finite field `F` and let `x : V →ₗ[F] V` be a
linear map whose minimal polynomial is irreducible.  Then `F[X]/(minpoly F x)` is a finite field,
and every element of `V ≃ₗ[F] V` which is a polynomial in `x` corresponds to an element of that
field.  A subgroup `H` all of whose elements are polynomials in `x` therefore embeds into the
multiplicative monoid of an integral domain, hence (being finite) is cyclic.

This is the `GL₂(F_q)` observation underlying the classification step: a subgroup of `GL₂(q)`
contained in a Singer cycle is cyclic. -/
theorem isCyclic_of_le_aeval {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {x : V →ₗ[F] V}
    (hirr : Irreducible (minpoly F x))
    (H : Subgroup (V ≃ₗ[F] V))
    (hH : ∀ a ∈ H, ∃ p : Polynomial F, Polynomial.aeval x p = (a : V →ₗ[F] V)) :
    IsCyclic ↥H := by
  classical
  -- `F[X]/(minpoly F x)` is a field, in particular an integral domain.
  haveI : Fact (Irreducible (minpoly F x)) := ⟨hirr⟩
  -- `H` is finite, being a subgroup of the finite group `V ≃ₗ[F] V`.
  have hVfin : Finite V := Module.finite_of_finite F
  have hGLfin : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) LinearEquiv.coe_injective
  have hHfin : Finite ↥H :=
    Finite.of_injective (fun a : ↥H => (a : V ≃ₗ[F] V)) (fun _ _ h => Subtype.ext h)
  -- The ring homomorphism `φ : F[X]/(minpoly F x) →+* End_F(V)` sending the class of `X` to `x`.
  let φ : AdjoinRoot (minpoly F x) →+* (V →ₗ[F] V) :=
    Ideal.Quotient.lift (Ideal.span {minpoly F x}) (Polynomial.aeval x).toRingHom (fun p hp => by
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      change Polynomial.aeval x (minpoly F x * q) = 0
      rw [map_mul, minpoly.aeval, zero_mul])
  -- Its value on the class of a polynomial `p` is `aeval x p`.
  have hφ_apply : ∀ p : Polynomial F,
      φ (AdjoinRoot.mk (minpoly F x) p) = Polynomial.aeval x p := by
    intro p
    show (Ideal.Quotient.lift _ _ _) ((Ideal.Quotient.mk _) p) = _
    rw [Ideal.Quotient.lift_mk]
    rfl
  -- `φ` is injective, since `aeval x p = 0` iff `minpoly F x ∣ p`.
  have hφ_inj : Function.Injective φ := by
    have hker : ∀ q : AdjoinRoot (minpoly F x), φ q = 0 → q = 0 := by
      intro q
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective q
      intro hq
      rw [hφ_apply p] at hq
      rw [AdjoinRoot.mk_eq_zero]
      exact minpoly.dvd F x hq
    intro a b hab
    have h : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker (a - b) h)
  -- Every `a ∈ H` is the image of some element of `F[X]/(minpoly F x)`.
  have hmem : ∀ a : ↥H, ∃ q : AdjoinRoot (minpoly F x), φ q = (a : V →ₗ[F] V) := by
    intro a
    obtain ⟨p, hp⟩ := hH a a.2
    exact ⟨AdjoinRoot.mk (minpoly F x) p, by rw [hφ_apply, hp]⟩
  -- The resulting injective multiplicative homomorphism `H → F[X]/(minpoly F x)`.
  let ψ : ↥H →* AdjoinRoot (minpoly F x) :=
    { toFun := fun a => Classical.choose (hmem a)
      map_one' := by
        apply hφ_inj
        rw [Classical.choose_spec (hmem 1), map_one]
        ext v
        simp
      map_mul' := fun a b => by
        apply hφ_inj
        rw [map_mul, Classical.choose_spec (hmem (a * b)),
          Classical.choose_spec (hmem a), Classical.choose_spec (hmem b)]
        ext v
        simp }
  have hψ_spec : ∀ a : ↥H, φ (ψ a) = (a : V →ₗ[F] V) :=
    fun a => Classical.choose_spec (hmem a)
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    have ha := hψ_spec a
    have hb := hψ_spec b
    have hcoe : (a : V →ₗ[F] V) = (b : V →ₗ[F] V) := by rw [← ha, ← hb, hab]
    exact Subtype.ext (LinearEquiv.ext (fun v => by
      simpa using congrArg (fun f : V →ₗ[F] V => f v) hcoe))
  -- A finite group admitting an injective homomorphism into an integral domain is cyclic.
  exact isCyclic_of_injective_ringHom ψ hψ_inj

end Work.ThmF.ChV12.Gl2Cyclic
