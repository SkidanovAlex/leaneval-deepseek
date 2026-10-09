import Mathlib
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.galToGamma_continuous
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi
import Submission.NK.Reconstruct.conjLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the outer action `τ^*` on `Γ_L`

Let `K` be a number field, `K'` a separable closure, `L ⊆ K'` a finite number-field level and
`θ : K' ≃+* K'` a ring automorphism preserving `L` as a set.  `NK.Reconstruct.tauStar` is a chosen
automorphism `τ^*` of `Γ_L = Gamma ↥L K' ℓ` with

  `τ^* (galToGamma g) = galToGamma (θ g θ⁻¹)`     for all `g : Gal(K'/L)`

(`NK.Reconstruct.tauStar_galToGamma`).  This file proves that this automorphism is
**continuous** for the profinite topology of `Γ_L`.

The argument is direct and does not depend on the particular choice of `τ^*`.  The topology of
`Γ_L` is the initial topology for the projections `Gamma.proj M : Γ_L → Γ_{M,ℓ}` onto the finite
(hence discrete) levels `M`; so it suffices to show that, for each level `M`, the composite

  `x ↦ Gamma.proj M (τ^* x)`

is continuous.  This composite is computed on the image of the surjection
`galToGamma : Gal(K'/L) →* Γ_L` (`NK.Reconstruct.galToGamma_surjective`), where
`τ^*(galToGamma g) = galToGamma (ringConjHom g)` and, at the level `M`,
`NK.Reconstruct.levelComponent_conj` expresses the ℓ-primary component of `θ g θ⁻¹` as the image
— under the level isomorphism `conjLevelAlgEquivHom L θ hθ M` — of the ℓ-primary component of `g`
at the conjugate level `θ⁻¹M = conjFrobLevel L θ hθ M`.  Since the ℓ-primary component of `g` at
`θ⁻¹M` is exactly `Gamma.proj (conjFrobLevel L θ hθ M) (galToGamma g)`, the composite factors as

  `x ↦ ℓ(Ab.map (conjLevelAlgEquivHom L θ hθ M) (proj (θ⁻¹M) x))`,

a function of `proj (θ⁻¹M) x` alone; the outer function is defined on a *discrete* finite group,
hence continuous, and `proj (θ⁻¹M)` is continuous (`NK.Reconstruct.continuous_proj`).

The one elementary input is `ellComp_map`: for a homomorphism `f` of finite abelian groups, the
ℓ-primary component of `f x` depends only on the ℓ-primary component of `x`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Prop. 4f.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- **A homomorphism of finite abelian groups respects the ℓ-primary projection**: the ℓ-primary
component of `f x` is the ℓ-primary component of the image of the ℓ-primary component of `x`.
Indeed `x` differs from `ellComp ℓ x` by an element of ℓ-coprime order, and `f` preserves
ℓ-coprimality of orders (`ellCoprimeRel_map`). -/
theorem ellComp_map {A B : Type*} [CommGroup A] [Finite A] [CommGroup B] [Finite B]
    (ℓ : ℕ) (f : A →* B) (x : A) :
    ellComp ℓ (f (ellComp ℓ x : A)) = ellComp ℓ (f x) :=
  ellComp_eq_of_ellCoprimeRel
    (ellCoprimeRel_symm (ellCoprimeRel_map f (ellCoprimeRel_ellComp ℓ x)))

/-- **Continuity of the outer action `τ^*`** (`NK.Reconstruct.tauStar`) on `Γ_L` for the
profinite topology. -/
theorem continuous_tauStar {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') [NumberField ↥L]
    (ℓ : ℕ) [Fact ℓ.Prime] (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) :
    Continuous ⇑(tauStar L ℓ θ hθ) := by
  classical
  haveI : IsGalois ↥L K' := inferInstance
  -- It suffices to check continuity of each projection `Gamma.proj M ∘ τ^*`.
  have hpiece : ∀ M : FrobLevel ↥L K',
      Continuous (fun x : Gamma ↥L K' ℓ => Gamma.proj M (tauStar L ℓ θ hθ x)) := by
    intro M
    -- `M₁ = θ⁻¹M` is the conjugate level: `conjLevelAlgEquivHom` is an isomorphism
    -- `Gal(θ⁻¹M/L) ≅ Gal(M/L)`.
    let M₁ : FrobLevel ↥L K' := conjFrobLevel L θ hθ M
    have hF : Continuous (fun y : LevelEllPart M₁.L ℓ =>
        ellComp ℓ (Abelianization.map (conjLevelAlgEquivHom L θ hθ M.L)
          (y : LevelAbelianization M₁.L))) := continuous_of_discreteTopology
    have hproj : Continuous (fun x : Gamma ↥L K' ℓ => Gamma.proj M₁ x) :=
      continuous_proj ℓ M₁
    -- The projection at `M` of `τ^* x` is a function of the projection of `x` at `θ⁻¹M` alone.
    have hkey : (fun x : Gamma ↥L K' ℓ => Gamma.proj M (tauStar L ℓ θ hθ x))
        = fun x => ellComp ℓ (Abelianization.map (conjLevelAlgEquivHom L θ hθ M.L)
            ((Gamma.proj M₁ x : LevelEllPart M₁.L ℓ) : LevelAbelianization M₁.L)) := by
      funext x
      obtain ⟨g, rfl⟩ := galToGamma_surjective (K := ↥L) (K' := K') ℓ x
      -- the defining property of `τ^*`, then the projection formula for `galToGamma`
      rw [tauStar_galToGamma L ℓ θ hθ g, galToGamma_proj]
      rw [show ringConjHom L θ hθ g = ringConjAlgEquiv L θ hθ g from rfl]
      -- `levelComponent_conj` at the level `M`, and the projection formula at `M₁`
      rw [levelComponent_conj L θ ℓ hθ M g, galToGamma_proj, levelComponent]
      exact (ellComp_map ℓ (Abelianization.map (conjLevelAlgEquivHom L θ hθ M.L))
        (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M₁.L g))).symm
    rw [hkey]
    exact hF.comp hproj
  -- Continuity into the projective limit is continuity of all the projections.
  refine (Topology.IsEmbedding.continuous_iff Topology.IsEmbedding.subtypeVal).mpr ?_
  exact continuous_pi (fun M => hpiece M)

end NK.Reconstruct
