import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.galToGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-!
# Continuity of the canonical map `G_K → Γ_K`

`galToGamma ℓ : Gal(K'/K) →* Gamma K K' ℓ` (`NK.Reconstruct.galToGamma`) is the map sending an
automorphism `g` to the coherent family of the ℓ-primary components of the restrictions of `g` to
the finite normal levels of `K'/K`.  The target `Γ_K = Gamma K K' ℓ` carries the subspace topology
of the product `∏_L Γ_{L,ℓ}` of the finite (hence discrete) level groups, and the source carries the
Krull topology.

The map is continuous, and the proof is the direct one: continuity into a product of discrete spaces
is checked on the components, and the component at the level `L` is

  `g ↦ ellComp ℓ (Abelianization.of (g|_L))`,

the composite of the ℓ-primary projection — continuous because its source `Gal(L/K)` is a *finite*
group, hence discrete — with the restriction map `AlgEquiv.restrictNormalHom L`, which is continuous
for the Krull topology by `InfiniteGalois.restrictNormalHom_continuous`.
-/

open scoped Pointwise

/-- **`galToGamma ℓ` is continuous** for the Krull topology on `Gal(K'/K)` and the profinite
(projective limit) topology on `Γ_K`. -/
theorem galToGamma_continuous {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) :
    Continuous ⇑(galToGamma (K := K) (K' := K') ℓ) := by
  -- Continuity into the projective limit is continuity of the family of the components: the
  -- topology of `Γ_K` is the subspace topology of the product of the finite levels.
  have hF : Continuous (fun g : Gal(K'/K) => fun L => levelComponent ℓ L g) := by
    refine continuous_pi (fun L => ?_)
    -- The component at `L` factors through the restriction `g ↦ g|_L`, which is continuous.
    have h1 : Continuous (fun g : Gal(K'/K) =>
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L.L g) :=
      InfiniteGalois.restrictNormalHom_continuous L.L
    -- The ℓ-primary projection is defined on the finite group `Gal(L/K)`, which is discrete.
    have h2 : Continuous (fun α : Gal(↥L.L/K) => ellComp ℓ (Abelianization.of α)) :=
      continuous_of_discreteTopology
    exact h2.comp h1
  exact Continuous.subtype_mk hF (fun g => levelComponent_compatible ℓ g)

end NK.Reconstruct
