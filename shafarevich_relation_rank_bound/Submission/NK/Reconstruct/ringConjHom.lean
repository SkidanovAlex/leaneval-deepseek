import Mathlib

/-!
# Conjugation of relative automorphisms by a ring automorphism of the ambient field

Let `K'` be a field, `L ⊆ K'` a subfield and `θ` a ring automorphism of `K'` which *preserves*
`L` (as a set).  Conjugation `g ↦ θ g θ⁻¹` by `θ` is then an automorphism of the group
`Gal(K'/L) = K' ≃ₐ[L] K'` of relative automorphisms.  This file provides that automorphism,
first on a single element (`NK.Reconstruct.ringConjAlgEquiv`) and then as a monoid homomorphism
(`NK.Reconstruct.ringConjHom`).

(The composition of `RingEquiv`s is written in Mathlib in the "application" order: `e₁.trans e₂`
acts as `x ↦ e₂ (e₁ x)`, so conjugation by `θ` is `θ.symm.trans (g.trans θ)`, cf.
`NK.Reconstruct.algEquivConjHom`.)

It is the input of Shimizu's `τ^*` (arXiv:2009.10431, §4, proof of Proposition 4f.3): for
`τ ∈ G(L/ℚ)` the *outer* action of `τ` on `Γ_L = (G_L^{ab,(ℓ)})^{tf}` is induced by this
conjugation on `G_L = Gal(Ω/L)`, well defined because inner automorphisms act trivially on the
abelianisation, and it is the twist with which the maps `π_{L/K}` are compared.

Nothing here uses number-field hypotheses: it is pure Galois theory of a field extension.
-/

namespace NK.Reconstruct

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']

/-- **Conjugation of a relative automorphism by a ring automorphism of the ambient field**: for
`θ : K' ≃+* K'` preserving the subfield `L`, the conjugate `θ g θ⁻¹` of `g ∈ Gal(K'/L)` is again
an `L`-automorphism of `K'` (it fixes `L` because `θ` preserves `L`). -/
noncomputable def ringConjAlgEquiv (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) : Gal(K'/↥L) :=
  { toRingEquiv := θ.symm.trans (g.toRingEquiv.trans θ)
    commutes' := fun c => by
      have hmem : θ.symm ((c : K')) ∈ L :=
        (hθ (θ.symm (c : K'))).mpr (by rw [RingEquiv.apply_symm_apply]; exact c.2)
      have hfix := AlgEquiv.commutes g (⟨θ.symm ((c : K')), hmem⟩ : ↥L)
      have hfix' : g.toRingEquiv (θ.symm ((c : K'))) = θ.symm ((c : K')) := hfix
      change θ (g.toRingEquiv (θ.symm ((c : K')))) = (c : K')
      rw [hfix', RingEquiv.apply_symm_apply] }

/-- **The defining formula of `ringConjAlgEquiv`**: `(θ g θ⁻¹) x = θ (g (θ⁻¹ x))`. -/
theorem ringConjAlgEquiv_apply (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) (x : K') :
    ringConjAlgEquiv L θ hθ g x = θ (g (θ.symm x)) := rfl

/-- The underlying ring equivalence of `ringConjAlgEquiv` is `θ g θ⁻¹`. -/
theorem ringConjAlgEquiv_toRingEquiv (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) :
    (ringConjAlgEquiv L θ hθ g).toRingEquiv = θ.symm.trans (g.toRingEquiv.trans θ) := rfl

/-- **Conjugation by a ring automorphism preserving a subfield**, as a monoid homomorphism of the
group of relative automorphisms. -/
noncomputable def ringConjHom (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) : Gal(K'/↥L) →* Gal(K'/↥L) where
  toFun := ringConjAlgEquiv L θ hθ
  map_one' := by
    ext x
    rw [ringConjAlgEquiv_apply]
    show θ ((1 : Gal(K'/↥L)) (θ.symm x)) = x
    rw [AlgEquiv.one_apply, RingEquiv.apply_symm_apply]
  map_mul' g h := by
    ext x
    simp only [ringConjAlgEquiv_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]

/-- **The defining formula of `ringConjHom`**. -/
theorem ringConjHom_apply (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) (x : K') :
    ringConjHom L θ hθ g x = θ (g (θ.symm x)) := rfl

/-- `ringConjHom` is injective. -/
theorem ringConjHom_injective (L : IntermediateField K K') (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) : Function.Injective (ringConjHom L θ hθ) := by
  intro g h hgh
  have h1 : ∀ u : K', g u = h u := by
    intro u
    have h2 : ringConjHom L θ hθ g (θ u) = ringConjHom L θ hθ h (θ u) :=
      congrArg (fun e : Gal(K'/↥L) => e (θ u)) hgh
    rw [ringConjHom_apply, ringConjHom_apply] at h2
    exact θ.injective (by simpa only [RingEquiv.symm_apply_apply] using h2)
  exact AlgEquiv.ext fun y => h1 y

end NK.Reconstruct
