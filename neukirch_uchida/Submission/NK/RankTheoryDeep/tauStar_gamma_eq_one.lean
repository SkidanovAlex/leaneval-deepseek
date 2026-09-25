import Mathlib
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.galToGamma

/-!
# `τ^* = 1` at the bottom level: an automorphism of `K'` fixing `K` acts trivially on `Γ_K`

`NK.Reconstruct.tauStar L ℓ θ hθ` is Shimizu's *outer* action of a ring automorphism `θ` of the
separable closure `K'` on the ℓ-adic abelianisation `Γ_L = Γ_{L,ℓ}`; it is characteristed by
`τ^*(galToGamma g) = galToGamma (θ g θ⁻¹)` for `g ∈ Gal(K'/L)`
(`NK.Reconstruct.tauStar_galToGamma`).

At the bottom level `L = ⊥` (i.e. `L = K`), an automorphism `θ` which preserves `K`
(`hθ`) and fixes it pointwise (`hfix`) is *an element of* `Gal(K'/K) = Gal(K'/⊥)`; the conjugation
`g ↦ θ g θ⁻¹` is therefore an **inner** automorphism, and inner automorphisms act trivially on the
abelianisation `Γ_K`.  Hence `τ^* = 1`:

  `NK.RankTheoryDeep.tauStar_gamma_eq_one`.

This is exactly the case needed when the "fixed" automorphism `Θ τ` of Shimizu's Proposition 4f.3 is
the identity on the base field: the twist `τ^*` drops out of the comparison of the maps `π_{L/K}`.

## The route

* `abelianization_of_conj` — conjugation is trivial in the abelianisation of a group;
* `galToGamma_ringConjHom_of_fixes` — if `θ` fixes a level `L` pointwise (and preserves it), then
  `galToGamma` is invariant under `ringConjHom L θ hθ`.  Indeed `θ` *is* an element `θA` of
  `Gal(K'/L)` and `ringConjHom L θ hθ g = θA * g * θA⁻¹`; restricting the identity to a finite
  level `M/L` and applying `Gal(M/L)^{ab}` (the ℓ-primary part of which is `Γ_{M,ℓ}`), conjugation
  becomes trivial by `abelianization_of_conj`;
* `tauStar` is determined by its values on the range of the surjective `galToGamma`, so
  `tauStar ⊥ ℓ θ hθ = 1`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Prop. 4f.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.RankTheoryDeep

open NK.Reconstruct

/-- **Conjugation is invisible in the abelianisation**: for `a b` in a group, the class of
`a b a⁻¹` in `Abelianization G` is the class of `b`. -/
theorem abelianization_of_conj {G : Type*} [Group G] (a b : G) :
    Abelianization.of a * Abelianization.of b * (Abelianization.of a)⁻¹ = Abelianization.of b := by
  rw [mul_comm (Abelianization.of a) (Abelianization.of b), mul_assoc, mul_inv_cancel, mul_one]

/-- **A ring automorphism of `K'` fixing a level `L` pointwise acts trivially on `Γ_L`.**

If `θ : K' ≃+* K'` preserves `L` (`hθ`) and fixes `L` pointwise (`hfixL`), then `θ` is an element
of `Gal(K'/L)`, so `ringConjHom L θ hθ` is an inner automorphism of `Gal(K'/L)`; inner
automorphisms act trivially on the abelianisation, whence the compatibility with the canonical map
`galToGamma : Gal(K'/L) →* Γ_L`. -/
theorem galToGamma_ringConjHom_of_fixes {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] (L : IntermediateField K K') [NumberField ↥L] [IsGalois ↥L K']
    (ℓ : ℕ) [Fact ℓ.Prime] (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (hfixL : ∀ c : ↥L, θ (algebraMap ↥L K' c) = algebraMap ↥L K' c) (g : Gal(K'/↥L)) :
    galToGamma (K := ↥L) (K' := K') ℓ (ringConjHom L θ hθ g)
      = galToGamma (K := ↥L) (K' := K') ℓ g := by
  classical
  -- `θ`, as an element of `Gal(K'/L)`
  let θA : Gal(K'/↥L) := { toRingEquiv := θ, commutes' := hfixL }
  have hconj : ringConjHom L θ hθ g = θA * g * θA⁻¹ := by
    ext x
    simp only [ringConjHom_apply, AlgEquiv.mul_apply]
    rfl
  refine Gamma.ext (fun M => ?_)
  rw [galToGamma_proj, galToGamma_proj, hconj]
  show ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M.L
        (θA * g * θA⁻¹)))
      = ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M.L g))
  rw [show Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M.L
          (θA * g * θA⁻¹))
      = Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M.L g) from by
    simp only [map_mul, map_inv]
    exact abelianization_of_conj _ _]

/-- **`τ^*` is trivial at the bottom level**: a ring automorphism of the separable closure `K'`
which preserves `K` and fixes it pointwise induces the identity on the ℓ-adic abelianisation
`Γ_K = Γ_{⊥,ℓ}`. -/
theorem tauStar_gamma_eq_one {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsGalois K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] (θ : K' ≃+* K')
    (hθ : ∀ x : K', x ∈ (⊥ : IntermediateField K K') ↔ θ x ∈ (⊥ : IntermediateField K K'))
    (hfix : ∀ k : K, θ (algebraMap K K' k) = algebraMap K K' k) :
    NK.Reconstruct.tauStar (⊥ : IntermediateField K K') ℓ θ hθ = 1 := by
  classical
  -- `θ` fixes the bottom level pointwise, because that level is the image of `K`
  have hfixL : ∀ c : ↥(⊥ : IntermediateField K K'),
      θ (algebraMap ↥(⊥ : IntermediateField K K') K' c)
        = algebraMap ↥(⊥ : IntermediateField K K') K' c := by
    intro c
    have hc : (c : K') ∈ (⊥ : IntermediateField K K') := c.2
    rw [IntermediateField.mem_bot] at hc
    obtain ⟨k, hk⟩ := hc
    show θ (c : K') = (c : K')
    rw [← hk]
    exact hfix k
  -- `τ^*` is determined by its values on the range of `galToGamma`, which is everything
  refine MulEquiv.ext (fun γ => ?_)
  obtain ⟨g, rfl⟩ := galToGamma_surjective (K := ↥(⊥ : IntermediateField K K')) (K' := K') ℓ γ
  rw [tauStar_galToGamma]
  exact galToGamma_ringConjHom_of_fixes ⊥ ℓ θ hθ hfixL g

end NK.RankTheoryDeep
