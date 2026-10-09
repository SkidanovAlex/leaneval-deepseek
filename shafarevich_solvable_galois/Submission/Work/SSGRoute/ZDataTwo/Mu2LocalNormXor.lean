import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalReciprocity.NormGroup
import Submission.Work.SSGRoute.ZDataTwo.LocalNormBadChar
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_iff_iff_of_biquadratic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The extension-variable half of the local Kummer dictionary, at a local field

The local norm condition of a quadratic extension of local fields is *bilinear*: besides its
multiplicativity in the point variable it is also multiplicative in the *extension* variable.  For
the three quadratic subfields `Λ₁, Λ₂, Λ₃ = Λ₁Λ₂`'s third quadratic subfield of a biquadratic
abelian extension of a local field `F`, the three local norm subgroups of `Fˣ` satisfy

  `N₃ = {x | (x ∈ N₁) ↔ (x ∈ N₂)}`

— equivalently, in `𝔽₂` terms, *the bad indicator of the third is the sum of the other two*, which
is the multiplicativity of the local Hilbert symbol in its first (extension) variable.

The proof has exactly two inputs:

* the Galois-theoretic Klein-four fact `mem_fixingSubgroup_iff_iff_of_biquadratic` about the
  fixing subgroups of the three quadratic sublevels (pure field theory);
* the reciprocity half of local class field theory, in the form `ArtinReciprocity.isLevelIso`:
  at a finite abelian level `Λ` the norm group `N_{Λ/F} Λˣ` is the preimage under the Artin map of
  the fixing subgroup of `Λ` (this is also the shape of the class-formation axiom
  `NK.LocalCFT.NormGroup.normGroup_sup_eq_inf`).

The transfer from here to the number-field-level condition `NK.NUV2.LC.IsLocalNorm` at a finite
prime `Q` is the plumbing `exists_level_normGroup_eq_of_quadratic` (realising the completion
`k_Q(√α)` as a quadratic level of `Gal(k_Q^ab/k_Q)`) together with the identification of the local
norm subgroup with the norm group of the completion extension.
-/

namespace Work.SSGRoute.ZDataTwo

/-- At a finite abelian level, the norm group is the preimage under the Artin map of the fixing
subgroup of the level. -/
lemma normGroup_eq_comap_fixingSubgroup
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (D : NK.LocalCFT.ArtinReciprocity F F')
    (Λ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F Λ] [Normal F Λ]
    (hc : ∀ σ τ : ↥Λ ≃ₐ[F] ↥Λ, σ * τ = τ * σ) :
    NK.LocalReciprocity.normGroup F ↥Λ = Λ.fixingSubgroup.comap D.artin := by
  rw [← (D.isLevelIso Λ hc).2, ← Λ.restrictNormalHom_ker, MonoidHom.comap_ker]
  congr 1

/-- **The extension-variable half of the local Kummer dictionary at a local field.**  For the three
quadratic sublevels of a biquadratic abelian extension, the local norm subgroups satisfy the
Klein-four relation: an element of `Fˣ` lies in the third norm group exactly when its membership in
the first two agrees.  (Equivalently: `x ∉ N₃ ↔ (x ∉ N₁) ⊕ (x ∉ N₂)`.) -/
theorem normGroup_iff_iff_of_biquadratic
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (D : NK.LocalCFT.ArtinReciprocity F F')
    (Λ₁ Λ₂ Λ₃ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F Λ₁] [Normal F Λ₁] [FiniteDimensional F Λ₂] [Normal F Λ₂]
    [FiniteDimensional F Λ₃] [Normal F Λ₃]
    (hcomm₁ : ∀ σ τ : ↥Λ₁ ≃ₐ[F] ↥Λ₁, σ * τ = τ * σ)
    (hcomm₂ : ∀ σ τ : ↥Λ₂ ≃ₐ[F] ↥Λ₂, σ * τ = τ * σ)
    (hcomm₃ : ∀ σ τ : ↥Λ₃ ≃ₐ[F] ↥Λ₃, σ * τ = τ * σ)
    (hgal : ∀ σ : NK.LocalCFT.AbGal F F',
      (σ ∈ Λ₃.fixingSubgroup) ↔ ((σ ∈ Λ₁.fixingSubgroup) ↔ (σ ∈ Λ₂.fixingSubgroup)))
    (x : Fˣ) :
    x ∈ NK.LocalReciprocity.normGroup F ↥Λ₃ ↔
      (x ∈ NK.LocalReciprocity.normGroup F ↥Λ₁ ↔ x ∈ NK.LocalReciprocity.normGroup F ↥Λ₂) := by
  rw [normGroup_eq_comap_fixingSubgroup D Λ₃ hcomm₃,
    normGroup_eq_comap_fixingSubgroup D Λ₁ hcomm₁,
    normGroup_eq_comap_fixingSubgroup D Λ₂ hcomm₂]
  simp only [Subgroup.mem_comap]
  exact hgal (D.artin x)

/-- **The bad indicator of the extension variable is additive.**  In the notation of
`normGroup_iff_iff_of_biquadratic`: `x` fails to be a local norm for the third level exactly when it
fails for exactly one of the first two — the multiplicativity of the local Hilbert symbol in its
first (extension) variable, in the form in which the product formula consumes it. -/
theorem not_mem_normGroup_iff_not_iff_of_biquadratic
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (D : NK.LocalCFT.ArtinReciprocity F F')
    (Λ₁ Λ₂ Λ₃ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F Λ₁] [Normal F Λ₁] [FiniteDimensional F Λ₂] [Normal F Λ₂]
    [FiniteDimensional F Λ₃] [Normal F Λ₃]
    (hcomm₁ : ∀ σ τ : ↥Λ₁ ≃ₐ[F] ↥Λ₁, σ * τ = τ * σ)
    (hcomm₂ : ∀ σ τ : ↥Λ₂ ≃ₐ[F] ↥Λ₂, σ * τ = τ * σ)
    (hcomm₃ : ∀ σ τ : ↥Λ₃ ≃ₐ[F] ↥Λ₃, σ * τ = τ * σ)
    (hgal : ∀ σ : NK.LocalCFT.AbGal F F',
      (σ ∈ Λ₃.fixingSubgroup) ↔ ((σ ∈ Λ₁.fixingSubgroup) ↔ (σ ∈ Λ₂.fixingSubgroup)))
    (x : Fˣ) :
    (x ∉ NK.LocalReciprocity.normGroup F ↥Λ₃) ↔
      ¬ ((x ∉ NK.LocalReciprocity.normGroup F ↥Λ₁) ↔
        (x ∉ NK.LocalReciprocity.normGroup F ↥Λ₂)) := by
  have h := normGroup_iff_iff_of_biquadratic D Λ₁ Λ₂ Λ₃ hcomm₁ hcomm₂ hcomm₃ hgal x
  tauto

/-- **The extension-variable half of the local Kummer dictionary, unconditional form.**  For the
three quadratic sublevels of a biquadratic abelian extension of a local field `F`, the local norm
condition is multiplicative in the extension variable: `x` lies in the third norm group exactly when
its membership in the first two agrees.  (In `𝔽₂` terms: the bad indicator of the third level is the
sum of the other two.)  This is the Klein-four computation
`mem_fixingSubgroup_iff_iff_of_biquadratic` transported along the Artin map by
`normGroup_eq_comap_fixingSubgroup`.

The commutativity hypotheses are automatic in the intended application (the three levels are
quadratic over `F`, hence abelian). -/
theorem normGroup_iff_iff_of_quadratic_levels
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (D : NK.LocalCFT.ArtinReciprocity F F')
    (Λ₁ Λ₂ Λ₃ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F Λ₁] [Normal F Λ₁] [FiniteDimensional F Λ₂] [Normal F Λ₂]
    [FiniteDimensional F Λ₃] [Normal F Λ₃]
    (hcomm₁ : ∀ σ τ : ↥Λ₁ ≃ₐ[F] ↥Λ₁, σ * τ = τ * σ)
    (hcomm₂ : ∀ σ τ : ↥Λ₂ ≃ₐ[F] ↥Λ₂, σ * τ = τ * σ)
    (hcomm₃ : ∀ σ τ : ↥Λ₃ ≃ₐ[F] ↥Λ₃, σ * τ = τ * σ)
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2)
    (h₃ : Module.finrank F ↥Λ₃ = 2) (h₁₂ : Λ₁ ≠ Λ₂)
    (hle : Λ₃ ≤ Λ₁ ⊔ Λ₂) (hne₁ : Λ₃ ≠ Λ₁) (hne₂ : Λ₃ ≠ Λ₂)
    (x : Fˣ) :
    x ∈ NK.LocalReciprocity.normGroup F ↥Λ₃ ↔
      (x ∈ NK.LocalReciprocity.normGroup F ↥Λ₁ ↔ x ∈ NK.LocalReciprocity.normGroup F ↥Λ₂) := by
  refine normGroup_iff_iff_of_biquadratic D Λ₁ Λ₂ Λ₃ hcomm₁ hcomm₂ hcomm₃ (fun σ => ?_) x
  exact mem_fixingSubgroup_iff_iff_of_biquadratic (F := F)
    (Ω := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) Λ₁ Λ₂ Λ₃ h₁ h₂ h₃ h₁₂ hle hne₁ hne₂ σ

/-- The same, in the additive (bad indicator) form used by the product formula. -/
theorem not_mem_normGroup_iff_not_iff_of_quadratic_levels
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (D : NK.LocalCFT.ArtinReciprocity F F')
    (Λ₁ Λ₂ Λ₃ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F Λ₁] [Normal F Λ₁] [FiniteDimensional F Λ₂] [Normal F Λ₂]
    [FiniteDimensional F Λ₃] [Normal F Λ₃]
    (hcomm₁ : ∀ σ τ : ↥Λ₁ ≃ₐ[F] ↥Λ₁, σ * τ = τ * σ)
    (hcomm₂ : ∀ σ τ : ↥Λ₂ ≃ₐ[F] ↥Λ₂, σ * τ = τ * σ)
    (hcomm₃ : ∀ σ τ : ↥Λ₃ ≃ₐ[F] ↥Λ₃, σ * τ = τ * σ)
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2)
    (h₃ : Module.finrank F ↥Λ₃ = 2) (h₁₂ : Λ₁ ≠ Λ₂)
    (hle : Λ₃ ≤ Λ₁ ⊔ Λ₂) (hne₁ : Λ₃ ≠ Λ₁) (hne₂ : Λ₃ ≠ Λ₂)
    (x : Fˣ) :
    (x ∉ NK.LocalReciprocity.normGroup F ↥Λ₃) ↔
      ¬ ((x ∉ NK.LocalReciprocity.normGroup F ↥Λ₁) ↔
        (x ∉ NK.LocalReciprocity.normGroup F ↥Λ₂)) := by
  have h := normGroup_iff_iff_of_quadratic_levels D Λ₁ Λ₂ Λ₃ hcomm₁ hcomm₂ hcomm₃
    h₁ h₂ h₃ h₁₂ hle hne₁ hne₂ x
  tauto

end Work.SSGRoute.ZDataTwo
