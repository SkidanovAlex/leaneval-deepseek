import Submission.NK.LocalCFT.Basic

/-!
# The classical inputs of local class field theory, in reduced form

`NK.LocalCFT.ArtinReciprocity F F'` (the corrected reciprocity datum, `Basic.lean`) bundles three
things: the canonical Artin map `Fˣ →* G_F^{ab}`, the reciprocity isomorphisms at the finite abelian
levels of `F^{ab}`, and the *existence theorem* (cofinality of the norm groups).  This module
isolates the last two as independent, classical inputs:

* `NK.LocalCFT.ExistenceTheorem F F'` — the **existence theorem of local class field theory**:
  the norm groups of the finite abelian extensions of `F` are cofinal among the finite-index
  subgroups of `Fˣ` (Serre, *Local Fields*, Ch. XI §2; Neukirch, *Algebraic Number Theory* V §4).
  Classically it is proved by Lubin–Tate theory (the Lubin–Tate formal group of a uniformiser of `F`
  produces, for every open finite-index subgroup `N ≤ Fˣ`, an abelian extension whose norm group is
  `N`).

* `NK.LocalCFT.ReciprocityLaw F F'` — the **reciprocity law**, in the *canonical, compatible*
  form: at every finite abelian Galois level `L ≤ F^{ab}` an isomorphism
  `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, compatible with restriction between levels.  Compatibility is the
  part that the weak existential form available elsewhere in this workspace does not provide; it is
  exactly the statement that the level isomorphisms are the restrictions of a single map
  `Fˣ →* Gal(F^{ab}/F)`, which is what `NK.LocalCFT.ArtinReciprocity.artin` asserts.

The point of the separation is that the Artin map into `Gal(F^{ab}/F)` is *not* extra data beyond the
compatible family of level isomorphisms: it is the inverse limit of that family.  That construction
(and hence the reduction of `ArtinReciprocity` to the two classical inputs above) is the content of
the theorem `NK.LocalCFT.nonempty_artinReciprocity_of_reciprocityLaw`.

## Main definitions

* `NK.LocalCFT.ExistenceTheorem F F'`;
* `NK.LocalCFT.ReciprocityLaw F F'` (with `NK.LocalCFT.ReciprocityLaw.levelEquiv` and
  `NK.LocalCFT.ReciprocityLaw.compat`).
-/

open scoped Classical

namespace NK.LocalCFT

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The existence theorem of local class field theory**: every finite-index subgroup of `Fˣ`
contains the norm group `N_{L/F} Lˣ` of a finite abelian extension `L` of `F` inside `F^{ab}`.

Equivalently (by the reciprocity isomorphism at the level `L`, which
`NK.LocalCFT.ArtinReciprocity.isLevelIso` provides): every finite quotient of `Fˣ` is the Galois
group of a finite abelian extension of `F`.  Classically this is the Lubin–Tate existence theorem. -/
def ExistenceTheorem (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  ∀ M : Subgroup Fˣ, M.FiniteIndex →
    ∃ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      (_ : FiniteDimensional F L) (_ : Normal F L)
      (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      NK.LocalReciprocity.normGroup F ↥L ≤ M

/-- **The existence theorem of local class field theory in its classical form, for *abstract*
extensions**: every finite-index subgroup `M ≤ Fˣ` contains the norm group `N_{L/F} Lˣ` of a finite
abelian Galois extension `L/F`.

This is the Lubin–Tate existence theorem as it appears in the literature (Serre, *Local Fields*,
Ch. XI §2 / Neukirch V §4): for every open subgroup of `Fˣ` of finite index there is an abelian
extension of `F` whose norm group is contained in it.  It is stated for abstract extensions, i.e.
without reference to a fixed separable closure, which is how the classical sources state it;
`NK.LocalCFT.existenceTheorem_of_abstract` transports it to the form
`NK.LocalCFT.ExistenceTheorem F F'` used by the reciprocity datum. -/
def ExistenceTheoremAbstract (F : Type u) [Field F] : Prop :=
  ∀ M : Subgroup Fˣ, M.FiniteIndex →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : IsGalois F L) (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      NK.LocalReciprocity.normGroup F L ≤ M

/-- The inclusion of norm groups for a smaller level, used to state the compatibility of the level
isomorphisms. -/
theorem normGroup_le_of_le {L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    (h : L₂ ≤ L₁) :
    NK.LocalReciprocity.normGroup F ↥L₁ ≤ NK.LocalReciprocity.normGroup F ↥L₂ := by
  letI : Algebra ↥L₂ ↥L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L₂ ↥L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact NK.LocalReciprocity.normGroup_le_of_tower

/-- **The reciprocity law in canonical (compatible) form.**  For every finite abelian Galois level
`L` of `F^{ab}`, an isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, and these isomorphisms are compatible
with the restriction maps between levels: this is what makes them the level maps of a single
homomorphism `Fˣ →* Gal(F^{ab}/F)` (a homomorphism to the inverse limit `Gal(F^{ab}/F)` of the
finite levels is exactly a compatible family of level maps). -/
structure ReciprocityLaw (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] where
  /-- the reciprocity isomorphism at a finite abelian level. -/
  levelEquiv : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L] (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L)
  /-- compatibility with restriction to a smaller level. -/
  compat : ∀ (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
      (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
      (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) (h : L₂ ≤ L₁) (x : Fˣ),
      levelRestrictLe h (levelEquiv L₁ h₁ (QuotientGroup.mk x)) =
        levelEquiv L₂ h₂
          (QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
            (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ)
            (normGroup_le_of_le h) (QuotientGroup.mk x))

end NK.LocalCFT
