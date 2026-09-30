import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Setup

open scoped TensorProduct

/-- **Base change of an integral algebra map along a tensor product.**

Let `t ∈ A` be such that every element of `A` is integral over `K[X]` via the map
`Polynomial.aeval t : Polynomial K →+* A` (e.g. `t` arises from a Noether normalisation of a
finitely generated `K`-algebra `A`, so that `A` is integral over `K[t]`).  Then for every
`K`-algebra `R`, the `K`-algebra map `Polynomial R →+* A ⊗[K] R` sending `X` to `t ⊗ₜ 1` and `r`
to `1 ⊗ₜ r` (`Polynomial.eval₂RingHom`) is integral: every element of `A ⊗[K] R` is integral over
`Polynomial R` through it.

Suggested route.
* Every element of `A ⊗[K] R` is a sum of elements `a ⊗ₜ r = (a ⊗ₜ 1) * (1 ⊗ₜ r)`
  (`TensorProduct.inductionOn`, `Algebra.TensorProduct.tmul_mul_tmul`); integrality is closed under
  `+` and `*` (`IsIntegral.add`, `IsIntegral.mul`).
* `1 ⊗ₜ r` is the image of `C r`, hence integral (`RingHom.isIntegralElem_map`).
* For `a ⊗ₜ 1`: from `ht`, i.e. `(aeval t).IsIntegralElem a`, and the ring hom
  `A →+* A ⊗[K] R`, `a ↦ a ⊗ₜ 1` (`RingHom.IsIntegralElem.map`), the element `a ⊗ₜ 1` is integral
  over the image of `Polynomial K → A ⊗[K] R`, which is contained in the image of the target map
  `Polynomial R → A ⊗[K] R`; transport integrality along `Polynomial.map (algebraMap K R)`
  (using `Polynomial.eval₂_map`), or set up the two `Algebra` structures with `letI` and use
  `IsIntegral.map_of_comp_eq` / `algebraMap_isIntegral_iff`. -/
theorem isIntegral_eval2RingHom_tmul {K : Type*} [CommRing K] {A : Type*} [CommRing A] [Algebra K A]
    {R : Type*} [CommRing R] [Algebra K R] (t : A)
    (ht : ((Polynomial.aeval t : Polynomial K →ₐ[K] A)).toRingHom.IsIntegral) :
    (Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom
      (t ⊗ₜ[K] (1 : R))).IsIntegral := by
  -- The map `a ↦ a ⊗ₜ 1`.
  let θ : A →+* A ⊗[K] R :=
    (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := R)).toRingHom
  -- The given map `aeval t`.
  let φ : Polynomial K →+* A := (Polynomial.aeval t : Polynomial K →ₐ[K] A).toRingHom
  -- The target map `Polynomial R →+* A ⊗[K] R`.
  let ψ : Polynomial R →+* A ⊗[K] R :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom
      (t ⊗ₜ[K] (1 : R))
  have hψ : ∀ p : Polynomial R,
      ψ p = Polynomial.eval₂ (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom
        (t ⊗ₜ[K] (1 : R)) p := fun p => rfl
  have hθ : ∀ x : A, θ x =
      (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := R)) x := fun x => rfl
  have hφ : ∀ p : Polynomial K, φ p = (Polynomial.aeval t : Polynomial K →ₐ[K] A) p :=
    fun p => rfl
  -- `ψ` restricted to `Polynomial K` (via `Polynomial.map (algebraMap K R)`) agrees with `θ ∘ φ`.
  have key : ψ.comp (Polynomial.mapRingHom (algebraMap K R)) = θ.comp φ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
      rw [hψ, Polynomial.eval₂_C, hφ, hθ, Polynomial.aeval_C]
      exact (Algebra.TensorProduct.includeRight (A := A) (B := R)).commutes a
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      rw [hψ, Polynomial.eval₂_X, hφ, Polynomial.aeval_X, hθ]
      rw [Algebra.TensorProduct.includeLeft_apply]
  change ψ.IsIntegral
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a r
    -- `a ⊗ₜ 1` is integral: transport `ht a` along `θ`.
    have ha : ψ.IsIntegralElem (a ⊗ₜ[K] 1) := by
      obtain ⟨p, hpmonic, hp0⟩ := ht a
      have hmap0 : Polynomial.eval₂ (θ.comp φ) (θ a) p = 0 := by
        rw [← Polynomial.hom_eval₂ p φ θ a, hp0, map_zero]
      refine ⟨Polynomial.map (Polynomial.mapRingHom (algebraMap K R)) p, ?_, ?_⟩
      · exact Polynomial.Monic.map _ hpmonic
      · rw [Polynomial.eval₂_map, key]
        exact hmap0
    -- `1 ⊗ₜ r` is the image of `C r`.
    have hr : ψ.IsIntegralElem (1 ⊗ₜ[K] r) := by
      have h := RingHom.isIntegralElem_map (f := ψ) (x := Polynomial.C r)
      rwa [show ψ (Polynomial.C r) = 1 ⊗ₜ[K] r from by
        rw [hψ, Polynomial.eval₂_C]; rfl] at h
    rw [show a ⊗ₜ[K] r = (a ⊗ₜ[K] 1) * (1 ⊗ₜ[K] r) from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    exact RingHom.IsIntegralElem.mul ψ ha hr
  · intro x y hx hy
    exact RingHom.IsIntegralElem.add ψ hx hy

end Work.SpecLin.Setup
