import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SpecLin.Core

open scoped TensorProduct

/-- **The preimage of an ideal under a retraction.**  If `ψ : B →+* N` is a ring homomorphism
admitting a section `s : N →+* B` (`ψ (s r) = r` for all `r`), then for every ideal `I` of `N`
the preimage `ψ⁻¹(I)` is the sum of the kernel of `ψ` and of the extension `s(I)` of `I` along
the section.

`⊇` is clear: `ker ψ ⊆ ψ⁻¹(I)` and `ψ (s i) = i ∈ I` for `i ∈ I`, so `s(I) ⊆ ψ⁻¹(I)`, and
`ψ⁻¹(I)` is an ideal.  For `⊆`, an `x` with `ψ x ∈ I` is `x = (x - s (ψ x)) + s (ψ x)`, and the
two summands lie in `ker ψ` resp. `s(I)`. -/
lemma comap_eq_ker_sup_map {B N : Type*} [CommRing B] [CommRing N]
    (ψ : B →+* N) (s : N →+* B) (h : ∀ r, ψ (s r) = r) (I : Ideal N) :
    I.comap ψ = RingHom.ker ψ ⊔ I.map s := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have h1 : x - s (ψ x) ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_sub, h]
      simp
    have h2 : s (ψ x) ∈ I.map s := Ideal.mem_map_of_mem s hx
    have h3 : x - s (ψ x) + s (ψ x) ∈ RingHom.ker ψ ⊔ I.map s :=
      add_mem (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [sub_add_cancel] at h3
  · apply sup_le
    · intro x hx
      rw [RingHom.mem_ker] at hx
      rw [Ideal.mem_comap]
      show ψ x ∈ I
      rw [hx]
      exact I.zero_mem
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap]
      show ψ (s r) ∈ I
      rw [h]
      exact hr

/-- **(D2-alg)** The section prime plus the fibre prime is the kernel of the residue evaluation. -/
theorem sectionPrime_sup_fibrePrime_eq_ker {K : Type u} [Field K] {A : Type u} [CommRing A]
    [IsDomain A] [Algebra K A] {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (φ : A →ₐ[K] R) :
    (RingHom.ker (Algebra.TensorProduct.lift (S := K) φ (AlgHom.id K R)
        (fun _ _ => Commute.all _ _)).toRingHom)
      ⊔ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A))
      = RingHom.ker ((IsLocalRing.residue R).comp
          (Algebra.TensorProduct.lift (S := K) φ (AlgHom.id K R)
            (fun _ _ => Commute.all _ _)).toRingHom) := by
  -- `ψ` is the "evaluation" `A ⊗_K R →_K R`, `a ⊗ r ↦ φ a * r`.
  let ψ : A ⊗[K] R →ₐ[K] R :=
    Algebra.TensorProduct.lift (S := K) φ (AlgHom.id K R) (fun _ _ => Commute.all _ _)
  -- It is a retraction of `includeRight : R →_K A ⊗_K R`.
  have hψs : ∀ r : R, ψ (Algebra.TensorProduct.includeRight (A := A) r) = r := by
    intro r
    simp [ψ, Algebra.TensorProduct.includeRight_apply]
  -- The kernel of the residue evaluation is the preimage of the maximal ideal.
  have hker : RingHom.ker ((IsLocalRing.residue R).comp ψ.toRingHom) =
      (IsLocalRing.maximalIdeal R).comap ψ.toRingHom := by
    rw [← RingHom.comap_ker (IsLocalRing.residue R) ψ.toRingHom, IsLocalRing.ker_residue]
  change RingHom.ker ψ.toRingHom ⊔
      (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A)) =
    RingHom.ker ((IsLocalRing.residue R).comp ψ.toRingHom)
  rw [hker, comap_eq_ker_sup_map ψ.toRingHom
    (Algebra.TensorProduct.includeRight (A := A)).toRingHom hψs]
  rfl

end Work.SpecLin.Core
