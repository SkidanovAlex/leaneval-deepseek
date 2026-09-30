import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Setup

open Polynomial TensorProduct

/-- **Injectivity of a polynomial ring after tensoring with a transcendental element.**

Let `t ∈ A` be transcendental over the field `K` (i.e. `Polynomial.aeval t` is injective) and let
`R` be a `K`-algebra.  Then the `K`-algebra map `Polynomial R →+* A ⊗[K] R` sending `X` to
`t ⊗ₜ 1` and `r` to `1 ⊗ₜ r` (`Polynomial.eval₂RingHom`) is injective.  No hypothesis on `R`
beyond commutativity is needed, because every module over the field `K` is flat.

Suggested route.
* `f := (Polynomial.aeval t : Polynomial K →ₐ[K] A).toLinearMap` is injective, and `R` is flat over
  the field `K`, so `Module.Flat.lTensor_preserves_injective_linearMap` gives injectivity of
  `f.lTensor R : R ⊗[K] Polynomial K →ₗ[K] R ⊗[K] A`.
* Identify `Polynomial R` with `R ⊗[K] Polynomial K` via `polyEquivTensor K R`
  (`polyEquivTensor R A : A[X] ≃ₐ[R] A ⊗[R] R[X]`, `polyEquivTensor_symm_apply_tmul_eq_smul`) and
  `R ⊗[K] A` with `A ⊗[K] R` via `Algebra.TensorProduct.comm`.
* Conclude by identifying the resulting injective composite with the target map, e.g. by checking
  both on the monomials `C r * X ^ i` (which span `Polynomial R` over `K`) and using
  `K`-linearity of both sides (`Polynomial.as_sum`/`Polynomial.induction_on`). -/
theorem injective_eval2RingHom_tmul {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {R : Type*} [CommRing R] [Algebra K R] (t : A)
    (ht : Function.Injective (Polynomial.aeval t : Polynomial K →ₐ[K] A)) :
    Function.Injective (Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom
      (t ⊗ₜ[K] (1 : R))) := by
  -- The composite `Polynomial R ≃ R ⊗[K] K[X] → R ⊗[K] A ≃ A ⊗[K] R`, which is injective because
  -- the middle map is the base change of the injective `aeval t` along the flat `K`-module `R`.
  let Θ : Polynomial R →ₐ[K] A ⊗[K] R :=
    ((Algebra.TensorProduct.comm K A R).symm : (R ⊗[K] A) →ₐ[K] (A ⊗[K] R)).comp
      ((Algebra.TensorProduct.map (S := K) (R := K) (AlgHom.id K R)
        (Polynomial.aeval t : Polynomial K →ₐ[K] A)).comp
        (polyEquivTensor K R).toAlgHom)
  -- Tensoring the injective `aeval t` with `R` (a flat `K`-module) stays injective.
  have hmap : Function.Injective
      (Algebra.TensorProduct.map (S := K) (R := K) (AlgHom.id K R)
        (Polynomial.aeval t : Polynomial K →ₐ[K] A)) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := R)
      ((Polynomial.aeval t : Polynomial K →ₐ[K] A)).toLinearMap ht
    have key : (Algebra.TensorProduct.map (S := K) (R := K) (AlgHom.id K R)
        (Polynomial.aeval t : Polynomial K →ₐ[K] A)).toLinearMap
        = (((Polynomial.aeval t : Polynomial K →ₐ[K] A)).toLinearMap).lTensor R := by
      apply TensorProduct.ext'
      intro r p
      simp [LinearMap.lTensor_tmul]
    rw [← key] at h
    exact h
  have hΘ : Function.Injective Θ :=
    (Algebra.TensorProduct.comm K A R).symm.injective.comp
      (hmap.comp (polyEquivTensor K R).injective)
  -- Both sides are ring homs `R[X] →+* A ⊗[K] R`, so it suffices to compare them on `C a` and `X`.
  have heq : (Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom
      (t ⊗ₜ[K] (1 : R))) = Θ.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [Θ]
    · simp [Θ]
  rw [heq]
  exact hΘ

end Work.SpecLin.Setup
