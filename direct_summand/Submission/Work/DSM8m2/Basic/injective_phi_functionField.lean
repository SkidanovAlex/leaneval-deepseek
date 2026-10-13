import Mathlib
import Submission.Work.DSMap.Mix2Fix

/-!
# Injectivity of `A → Γ(X, ⊤) → K(X)` for `X` integral surjective over `Spec A`

Let `A` be a domain, `X` an integral scheme and `f : X ⟶ Spec A` surjective.  Then the
composite `A --φ--> Γ(X, ⊤) --germ at the generic point--> K(X)` is injective.

The proof has three steps.

* The map `φ = DSMap.phi A X f` is the transpose of `f` under the `Γ ⊣ Spec` adjunction, so
  the unit triangle identity gives `f = X.toSpecΓ ≫ Spec.map φ`.  Since `f` is surjective,
  `Spec.map φ` is surjective as well.
* `Spec.map φ` surjects onto `Spec A`; in particular the generic point `⊥` of `Spec A`
  (here `⊥ : Ideal A` is prime because `A` is a domain) has a preimage `q`, i.e.
  `Ideal.comap φ q = ⊥`.  Then `ker φ ⊆ comap φ q = ⊥`, so `φ` is injective.
* `germToFunctionField X ⊤` is injective since `X` is integral, and the composite of two
  injective maps is injective.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

-- The scheme-theoretic `Spec`, `Γ` and `Opposite` involve semireducible definitions; the
-- arguments below move between `Spec R` and `PrimeSpectrum R` and need the legacy defeq.
set_option backward.isDefEq.respectTransparency false

namespace Work.DSM8m2.Basic

theorem injective_phi_functionField {A : Type u} [CommRing A] [IsDomain A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsIntegral X] [Nonempty (⊤ : X.Opens)]
    (hs : Function.Surjective f) :
    Function.Injective ((AlgebraicGeometry.Scheme.germToFunctionField X ⊤).hom.comp (DSMap.phi A X f)) := by
  -- The transpose `φ` of `f` under `Γ ⊣ Spec`, as a morphism of `CommRingCat`.
  have hφop : (CommRingCat.ofHom (DSMap.phi A X f)).op =
      (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of A))).symm f := by
    rw [show CommRingCat.ofHom (DSMap.phi A X f) =
        ((ΓSpec.adjunction.homEquiv X (op (CommRingCat.of A))).symm f).unop from by
      rw [CommRingCat.hom_ext_iff]; rfl,
      Quiver.Hom.op_unop]
  -- Step 1: `f` factors as `X.toSpecΓ ≫ Spec.map φ` (unit triangle of the `Γ ⊣ Spec` adjunction).
  have hmain : X.toSpecΓ ≫ Scheme.Spec.map ((CommRingCat.ofHom (DSMap.phi A X f)).op) = f := by
    rw [← ΓSpec.adjunction_unit_app, ← Adjunction.homEquiv_unit, hφop]
    exact Equiv.apply_symm_apply _ f
  -- Step 2: hence `Spec.map φ` is surjective.
  have hsurj : Function.Surjective (Scheme.Spec.map ((CommRingCat.ofHom (DSMap.phi A X f)).op)) := by
    have hf' : Function.Surjective
        ⇑(X.toSpecΓ ≫ Scheme.Spec.map ((CommRingCat.ofHom (DSMap.phi A X f)).op)) := by
      rw [hmain]; exact hs
    refine Function.Surjective.of_comp (g := ⇑X.toSpecΓ) ?_
    rw [show (⇑(Scheme.Spec.map ((CommRingCat.ofHom (DSMap.phi A X f)).op)) ∘ ⇑X.toSpecΓ)
        = ⇑(X.toSpecΓ ≫ Scheme.Spec.map ((CommRingCat.ofHom (DSMap.phi A X f)).op)) from
        funext fun x => (Scheme.Hom.comp_apply _ _ x).symm]
    exact hf'
  -- Step 3: `Spec.map φ` hits the generic point of `Spec A`, forcing `ker φ = ⊥`.
  have hinjφr : Function.Injective (DSMap.phi A X f) := by
    have h2 : Function.Surjective ⇑(Spec.map (CommRingCat.ofHom (DSMap.phi A X f))) := by
      simpa [Scheme.Spec_map] using hsurj
    obtain ⟨q, hq⟩ := h2 (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A)
    have hq2 : Ideal.comap (DSMap.phi A X f) q.asIdeal = ⊥ := by
      have h1 := congrArg PrimeSpectrum.asIdeal hq
      rw [Spec.map_apply] at h1
      rw [PrimeSpectrum.comap_asIdeal] at h1
      simpa using h1
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm _ bot_le
    rw [← hq2]
    intro a ha
    rw [RingHom.mem_ker] at ha
    rw [Ideal.mem_comap, ha]
    exact q.asIdeal.zero_mem
  -- Step 4: compose with the injective germ at the generic point.
  have hgerm : Function.Injective ⇑(Scheme.germToFunctionField X ⊤).hom :=
    Scheme.germToFunctionField_injective X ⊤
  simpa only [RingHom.coe_comp] using hgerm.comp hinjφr

end Work.DSM8m2.Basic
