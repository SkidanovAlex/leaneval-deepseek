import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Submission.NK.Reconstruct.continuous_tauStar
import Submission.NK.Reconstruct.gammaBaseChangeHom_galToGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the isomorphism `Γ_{K₁} ≃* Γ_{K₂}` induced by `ϕ`

`NK.Reconstruct.exists_gammaEquivOfPhi` produces, for a homeomorphic isomorphism
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of absolute Galois groups, an isomorphism of abelianised
profinite groups `e : Γ_{K₁} ≃* Γ_{K₂}` characterised by

  `e (galToGamma g) = galToGamma (ϕ g)`     for all `g : Gal(K₁'/K₁)`

(and dually for `ϕ.symm`).  Since `Γ_{K₁}` is the *profinite* group in which Shimizu's §4 argument
takes place, the isomorphism must be shown to be a homeomorphism, not merely a group isomorphism;
this file supplies that continuity.

## The argument

Each `Γ_K` carries the subspace topology of the product `∏_L Γ_{L,ℓ}` of the finite (discrete)
level groups, so continuity of `e` is continuity of every component
`x ↦ Gamma.proj M (e x)` (`Topology.IsEmbedding.subtypeVal`, `continuous_pi`).

For a fixed level `M` of `K₂'/K₂`, the canonical map `galToGamma ℓ : Gal(K₁'/K₁) →* Γ_{K₁}` is a
*quotient map*: it is continuous (`galToGamma_continuous`) and surjective
(`galToGamma_surjective`) out of a compact space into a Hausdorff space
(`Topology.IsQuotientMap.of_surjective_continuous`).  Hence it suffices to check continuity after
precomposition with `galToGamma ℓ`, where the characterising property of `e` computes the composite:

  `g ↦ Gamma.proj M (e (galToGamma g)) = Gamma.proj M (galToGamma (ϕ g)) = levelComponent ℓ M (ϕ g)`,

and the latter is continuous as the composite of the continuous `ϕ`, the continuous restriction
`AlgEquiv.restrictNormalHom M` (`InfiniteGalois.restrictNormalHom_continuous`), and the ℓ-primary
projection out of the *finite* (hence discrete) group `Gal(↥M/K₂)`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

namespace NK.Reconstruct

theorem exists_gammaEquivOfPhi_continuous {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (ℓ : ℕ) :
    ∃ e : Gamma K₁ K₁' ℓ ≃* Gamma K₂ K₂' ℓ, Continuous ⇑e ∧
      (∀ g : Gal(K₁'/K₁),
        e (galToGamma (K := K₁) (K' := K₁') ℓ g)
          = galToGamma (K := K₂) (K' := K₂') ℓ (ϕ g)) ∧
      (∀ g : Gal(K₂'/K₂),
        e.symm (galToGamma (K := K₂) (K' := K₂') ℓ g)
          = galToGamma (K := K₁) (K' := K₁') ℓ (ϕ.symm g)) := by
  obtain ⟨e, he₁, he₂⟩ := exists_gammaEquivOfPhi ϕ hϕ ℓ
  refine ⟨e, ?_, he₁, he₂⟩
  -- `galToGamma ℓ : Gal(K₁'/K₁) →* Γ_{K₁}` is a quotient map.
  have hq : Topology.IsQuotientMap ⇑(galToGamma (K := K₁) (K' := K₁') ℓ) :=
    Topology.IsQuotientMap.of_surjective_continuous (galToGamma_surjective ℓ)
      (galToGamma_continuous ℓ)
  -- It suffices to check continuity of every component of `e`.
  refine (Topology.IsEmbedding.continuous_iff Topology.IsEmbedding.subtypeVal).mpr ?_
  rw [show (Subtype.val ∘ ⇑e) = fun x (M : FrobLevel K₂ K₂') => Gamma.proj M (e x) from rfl]
  refine continuous_pi (fun M => ?_)
  -- The component factors through the quotient map, where it is computed by `he₁`.
  refine (hq.continuous_iff).mpr ?_
  have hcomp : ((fun x => Gamma.proj M (e x)) ∘ ⇑(galToGamma (K := K₁) (K' := K₁') ℓ))
      = fun g : Gal(K₁'/K₁) => levelComponent ℓ M (ϕ g) := by
    funext g
    simp only [Function.comp_apply]
    rw [he₁ g, galToGamma_proj]
  rw [hcomp]
  -- `g ↦ levelComponent ℓ M (ϕ g)` is a composite of continuous maps, the last one out of a finite
  -- (hence discrete) group.
  have hcont : Continuous (fun y : Gal(↥M.L/K₂) => ellComp ℓ (Abelianization.of y)) :=
    continuous_of_discreteTopology
  exact hcont.comp ((InfiniteGalois.restrictNormalHom_continuous M.L).comp hϕ.continuous)

end NK.Reconstruct
