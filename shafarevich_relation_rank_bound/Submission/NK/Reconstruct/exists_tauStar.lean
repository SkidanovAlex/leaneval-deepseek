import Mathlib
import Submission.NK.Reconstruct.conjLevel
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi

/-!
# The outer action `τ^*` of a ring automorphism of `K'` on `Γ_L` (Shimizu, Prop. 4f.3)

Let `K` be a number field, `K'` a separable closure, `L ⊆ K'` a finite (number-field) level and
`θ : K' ≃+* K'` a ring automorphism preserving `L` as a set.  This file proves the existence of the
*outer* action of `θ` (i.e. of `θ|_L`) on the ℓ-adic abelianisation `Γ_L`:

  `exists_tauStar`:  there is a group automorphism `τstar` of `Γ_L = Gamma ↥L K' ℓ` with
  `τstar (galToGamma g) = galToGamma (θ g θ⁻¹)`  for every `g : Gal(K'/L)`.

Arithmetically, the conjugation map `g ↦ θ g θ⁻¹` is an automorphism of `G_L` which does *not*
preserve the base `L` pointwise, so it is not inner; but its effect on the abelianisation depends
only on `θ|_L`, whence a well-defined automorphism `τ^*` of `Γ_L`.  It is the twist with which
Shimizu compares the maps `π_{L/K}`, hence a prerequisite of Proposition 4f.3.

## The route

`galToGamma ℓ : Gal(K'/L) →* Γ_L` is surjective (`NK.Reconstruct.galToGamma_surjective`), so an
automorphism of `Γ_L` compatible with `galToGamma` exists exactly when `ringConjHom L θ hθ`
preserves the kernel of `galToGamma ℓ`; then one descends to the quotient `G_L ⧸ ker` (which is
`Γ_L` by the first isomorphism theorem) and transports the induced automorphism of the quotient
along `QuotientGroup.quotientKerEquivOfSurjective`.

The levelwise input is `NK.Reconstruct.conjLevelAlgEquivHom_restrictNormalHom`: the restriction of
`g` to the level `θ⁻¹M`, conjugated by `θ`, is the restriction of `θ g θ⁻¹` to `M`
(`NK.Reconstruct.conjLevel` builds the level `θ⁻¹M` and its conjugate action).

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']
  (L : IntermediateField K K') [NumberField ↥L]
  (θ : K' ≃+* K')

/-- **The ℓ-primary component of a conjugate is the conjugate of the ℓ-primary component**: at
the level `M`, the component of `θ g θ⁻¹` is the image under the level isomorphism
`Gal(θ⁻¹M/L) →* Gal(M/L)` of the component of `g` at the conjugate level `θ⁻¹M`.  This is
`conjLevelAlgEquivHom_restrictNormalHom` transported to the ℓ-primary parts, using the functoriality
of the abelianisation. -/
theorem levelComponent_conj (ℓ : ℕ) (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : FrobLevel ↥L K') (g : Gal(K'/↥L)) :
    levelComponent ℓ M (ringConjAlgEquiv L θ hθ g)
      = ellComp ℓ (Abelianization.map (conjLevelAlgEquivHom L θ hθ M.L)
          (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K')
            (conjLevel L θ hθ M.L) g))) := by
  rw [levelComponent, ← conjLevelAlgEquivHom_restrictNormalHom L θ hθ M g,
    Abelianization.map_of]

/-- **`ringConjHom L θ hθ` preserves the kernel of `galToGamma ℓ`.**

Indeed `galToGamma ℓ g = 1` iff the ℓ-primary component `levelComponent ℓ M g` vanishes at every
finite normal level `M` of `K'/L`.  At the level `M`, the component of `θ g θ⁻¹` is the image
(under a homomorphism of finite abelian groups, hence sending ℓ-primary components to ℓ-primary
components) of the component of `g` at the conjugate level `θ⁻¹M = conjLevel L θ hθ M.L`, which is
one of the levels on which `g` has vanishing component. -/
theorem ker_galToGamma_le_conj (ℓ : ℕ) (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) :
    (galToGamma (K := ↥L) (K' := K') ℓ).ker ≤
      (galToGamma (K := ↥L) (K' := K') ℓ).ker.comap (ringConjHom L θ hθ) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  refine Gamma.ext (fun M => ?_)
  rw [galToGamma_proj, map_one]
  have hN : levelComponent ℓ (conjFrobLevel L θ hθ M) g = 1 := by
    rw [← galToGamma_proj (K := ↥L) (K' := K') ℓ (conjFrobLevel L θ hθ M) g, hg, map_one]
  show levelComponent ℓ M (ringConjAlgEquiv L θ hθ g) = 1
  rw [levelComponent_conj L θ ℓ hθ M g, ← Abelianization.map_of]
  exact ellComp_map_eq_one ℓ (Abelianization.map (conjLevelAlgEquivHom L θ hθ M.L)) hN

/-- `ringConjHom L θ hθ` and `ringConjHom L θ⁻¹ (hθ_symm …)` are inverse to each other. -/
theorem ringConjHom_symm_comp (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) :
    ringConjHom L θ.symm (hθ_symm L θ hθ) (ringConjHom L θ hθ g) = g := by
  ext x
  simp [ringConjHom_apply]

/-- The other composition of the two conjugate actions. -/
theorem ringConjHom_symm_comp' (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) :
    ringConjHom L θ hθ (ringConjHom L θ.symm (hθ_symm L θ hθ) g) = g := by
  ext x
  simp [ringConjHom_apply]

theorem exists_tauStar {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') [NumberField ↥L] (ℓ : ℕ)
    (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) :
    ∃ τstar : Gamma ↥L K' ℓ ≃* Gamma ↥L K' ℓ,
      ∀ g : Gal(K'/↥L),
        τstar (galToGamma (K := ↥L) (K' := K') ℓ g)
          = galToGamma (K := ↥L) (K' := K') ℓ (ringConjHom L θ hθ g) := by
  classical
  haveI : IsGalois ↥L K' := inferInstance
  have hsurj : Function.Surjective ⇑(galToGamma (K := ↥L) (K' := K') ℓ) :=
    galToGamma_surjective (K := ↥L) (K' := K') ℓ
  let f := galToGamma (K := ↥L) (K' := K') ℓ
  have hθs : ∀ x : K', x ∈ L ↔ θ.symm x ∈ L := hθ_symm L θ hθ
  have hker : f.ker ≤ f.ker.comap (ringConjHom L θ hθ) := ker_galToGamma_le_conj L θ ℓ hθ
  have hker' : f.ker ≤ f.ker.comap (ringConjHom L θ.symm hθs) :=
    ker_galToGamma_le_conj L θ.symm ℓ hθs
  -- the induced map on the quotient `G_L ⧸ ker = Γ_L`
  let e₁ : Gamma ↥L K' ℓ ≃* (Gal(K'/↥L) ⧸ f.ker) :=
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm
  let Φ : Gamma ↥L K' ℓ →* Gamma ↥L K' ℓ :=
    e₁.symm.toMonoidHom.comp
      ((QuotientGroup.map f.ker f.ker (ringConjHom L θ hθ) hker).comp e₁.toMonoidHom)
  let Ψ : Gamma ↥L K' ℓ →* Gamma ↥L K' ℓ :=
    e₁.symm.toMonoidHom.comp
      ((QuotientGroup.map f.ker f.ker (ringConjHom L θ.symm hθs) hker').comp e₁.toMonoidHom)
  have hΦ : ∀ g : Gal(K'/↥L), Φ (f g) = f (ringConjHom L θ hθ g) := by
    intro g
    show e₁.symm ((QuotientGroup.map f.ker f.ker (ringConjHom L θ hθ) hker) (e₁ (f g))) = _
    have h₁ : e₁ (f g) = (g : Gal(K'/↥L) ⧸ f.ker) := by
      rw [← QuotientGroup.kerLift_mk f g]
      exact MulEquiv.symm_apply_apply (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
        (g : Gal(K'/↥L) ⧸ f.ker)
    rw [h₁, QuotientGroup.map_mk]
    exact QuotientGroup.kerLift_mk f (ringConjHom L θ hθ g)
  have hΨ : ∀ g : Gal(K'/↥L), Ψ (f g) = f (ringConjHom L θ.symm hθs g) := by
    intro g
    show e₁.symm ((QuotientGroup.map f.ker f.ker (ringConjHom L θ.symm hθs) hker') (e₁ (f g))) = _
    have h₁ : e₁ (f g) = (g : Gal(K'/↥L) ⧸ f.ker) := by
      rw [← QuotientGroup.kerLift_mk f g]
      exact MulEquiv.symm_apply_apply (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
        (g : Gal(K'/↥L) ⧸ f.ker)
    rw [h₁, QuotientGroup.map_mk]
    exact QuotientGroup.kerLift_mk f (ringConjHom L θ.symm hθs g)
  have hcomp₁ : Ψ.comp Φ = MonoidHom.id (Gamma ↥L K' ℓ) := by
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨g, rfl⟩ := hsurj x
    rw [MonoidHom.comp_apply, hΦ, hΨ, ringConjHom_symm_comp L θ hθ g]
    rfl
  have hcomp₂ : Φ.comp Ψ = MonoidHom.id (Gamma ↥L K' ℓ) := by
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨g, rfl⟩ := hsurj x
    rw [MonoidHom.comp_apply, hΨ, hΦ, ringConjHom_symm_comp' L θ hθ g]
    rfl
  let e : Gamma ↥L K' ℓ ≃* Gamma ↥L K' ℓ :=
    { toFun := Φ
      invFun := Ψ
      left_inv := fun x => by
        have h := DFunLike.congr_fun hcomp₁ x
        simpa using h
      right_inv := fun x => by
        have h := DFunLike.congr_fun hcomp₂ x
        simpa using h
      map_mul' := Φ.map_mul }
  exact ⟨e, fun g => hΦ g⟩
end NK.Reconstruct