import Mathlib.FieldTheory.Galois.Basic
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.Functoriality.levelMulEquiv_restrict
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_sup_eq_inf
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/LocalArtin/` — local class field theory, deliverable form

This is the entry file of the `NK.LocalArtin` chapter.  It fixes the *vocabulary* in which the
rest of the chapter (and the consumer, `NK.PTorsionTop.LocalGaloisInputsTop`) speaks, and
introduces the two structures in terms of which the reciprocity datum is reduced:

* `NK.LocalArtin.ReciprocityMap F F'` — **the reciprocity half** of local class field theory: a
  single homomorphism `artin : Fˣ →* Gal(F^{ab}/F)` whose composite with the restriction to every
  finite abelian Galois level `L ≤ F^{ab}` is surjective with kernel the norm group
  `N_{L/F} Lˣ`.  This is `NK.LocalCFT.ArtinReciprocity` with the existence theorem (`cofinal`)
  removed.
* `NK.LocalArtin.KernelCondition F F'` — the *weaker* single statement that such a map exists
  whose level kernels are the norm groups (no surjectivity demanded; it is *proved* below from
  the norm index theorem).
* `NK.LocalArtin.NormIndex F F'` — the **norm index theorem** `[Fˣ : N_{L/F} Lˣ] = [L : F]` for
  every finite abelian Galois level, a statement about cardinalities only, with no map in it.
* `NK.LocalArtin.LocalResidual F F'` — the **residual**: the reciprocity map together with the
  existence theorem (cofinality of the norm groups), i.e. the two classical theorems of local
  class field theory (Lubin–Tate/Honda plus the existence theorem).

## The main line of the chapter

```
KernelCondition + NormIndex  ⟹  ReciprocityMap  ⟹ (+ ExistenceTheorem)  ArtinReciprocity
```

Everything except `KernelCondition`, `NormIndex` and `ExistenceTheorem` is *proved*.  For the
archimedean local field `ℝ` all three are discharged unconditionally
(`NK.LocalCFT.Instance.artinReciprocity_complex`); for a `p`-adic field they are the residual
of the chapter.

## The conventions inherited from `NK.LocalCFT`

* `NK.LocalArtin.AbsGal F F' = Gal(F'/F) = (F' ≃ₐ[F] F')`;
* `NK.LocalArtin.AbGal F F' = Gal(F^{ab}/F)`, where `F^{ab} = maxAbelianSubext F F'` is the
  fixed field of the commutator subgroup of `Gal(F'/F)`;
* `NK.LocalArtin.normGroup F E = N_{E/F} Eˣ ≤ Fˣ`, the image of the norm map on units;
* a *level* of `F^{ab}` is an intermediate field `L ≤ F^{ab}` which is finite-dimensional and
  normal over `F` (its Galois group is then automatically commutative, because it is a quotient
  of the commutative group `Gal(F^{ab}/F)`).

The existence theorem is *not* part of `ReciprocityMap`; that separation is what makes the two
halves of local class field theory independently statable, and it is used in
`NK.LocalArtin.Reduction`.
-/

open scoped Classical

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace NK.LocalArtin

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-- The absolute Galois group `G_F = Gal(F'/F)`. -/
abbrev AbsGal (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] :=
  NK.LocalCFT.AbsGal F F'

/-- The abelianised absolute Galois group `G_F^{ab} = Gal(F^{ab}/F)`. -/
abbrev AbGal (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] :=
  NK.LocalCFT.AbGal F F'

/-- The maximal abelian subextension `F^{ab} ≤ F'` of `F'/F` (the fixed field of the commutator
subgroup of `Gal(F'/F)`). -/
abbrev maxAbelianSubext (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] :=
  NK.LocalReciprocity.maxAbelianSubext F F'

/-- The norm group `N_{E/F} Eˣ ≤ Fˣ`, the image of the norm map on unit groups. -/
abbrev normGroup (F E : Type*) [Field F] [Field E] [Algebra F E] : Subgroup Fˣ :=
  NK.LocalReciprocity.normGroup F E

variable [IsGalois F F']

/-- The restriction `Gal(F^{ab}/F) →* Gal(L/F)` for a normal level `L ≤ F^{ab}`. -/
abbrev levelRestrict (L : IntermediateField F (maxAbelianSubext F F')) [Normal F L] :
    AbGal F F' →* (↥L ≃ₐ[F] ↥L) :=
  NK.LocalCFT.levelRestrict L

/-- **The reciprocity half of local class field theory.**

A `ReciprocityMap F F'` is a single homomorphism `artin : Fˣ →* Gal(F^{ab}/F)` such that, at every
finite abelian Galois level `L ≤ F^{ab}`, the composite

`Fˣ --artin--> Gal(F^{ab}/F) --restriction--> Gal(L/F)`

is surjective with kernel the norm group `N_{L/F} Lˣ`.

This is `NK.LocalCFT.ArtinReciprocity` with the existence theorem (`cofinal`) removed; the
reciprocity law proper says that such a map exists, and the existence theorem says that its
norm groups are cofinal among the finite-index subgroups of `Fˣ`. -/
structure ReciprocityMap (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] where
  /-- the Artin map `Fˣ →* Gal(F^{ab}/F)`. -/
  artin : Fˣ →* AbGal F F'
  /-- at every finite abelian level the Artin map is surjective with kernel the norm group. -/
  isLevelIso : ∀ (L : IntermediateField F (maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L] (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      Function.Surjective ((levelRestrict L).comp artin) ∧
        MonoidHom.ker ((levelRestrict L).comp artin) = normGroup F ↥L

/-- **The existence theorem** (a re-export of `NK.LocalCFT.ExistenceTheorem`): the norm groups of
the finite abelian extensions of `F` are cofinal among the finite-index subgroups of `Fˣ`.

This is the Lubin–Tate existence theorem; it is the second half of local class field theory. -/
abbrev ExistenceTheorem (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  NK.LocalCFT.ExistenceTheorem F F'

/-- **The residual of the chapter**: the two classical theorems of local class field theory,
namely the reciprocity law (in the single-map form `ReciprocityMap`) and the existence theorem.

`NK.LocalArtin.nonempty_artinReciprocity_of_residual` turns this into
`Nonempty (NK.LocalCFT.ArtinReciprocity F F')`, and it is exactly the content that the
`p`-adic case leaves unproved (`NK.LocalArtin.Padic`). -/
structure LocalResidual (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop where
  /-- the reciprocity law: the existence of an Artin map with the correct finite level behaviour. -/
  reciprocity : Nonempty (ReciprocityMap F F')
  /-- the existence theorem: cofinality of the norm groups. -/
  existence : ExistenceTheorem F F'

/-- **The norm index theorem**, in the form in which the chapter consumes it: at every finite
abelian Galois level `L ≤ F^{ab}`, the norm group `N_{L/F} Lˣ` has index `[L : F]` in `Fˣ`.

This is a statement about cardinalities alone — no Artin map occurs in it.  For a `p`-adic field it
is the Herbrand-quotient computation `Ĥ⁰(Gal(L/F), Lˣ) ≅ ℤ/[L:F]`, and it is a *consequence* of
the reciprocity law (`NK.LocalArtin.normIndex_of_reciprocityMap`); the point of isolating it is
that together with `KernelCondition` it *produces* the surjectivity of the Artin map
(`NK.LocalArtin.ReciprocityMap.of_kernelCondition`). -/
def NormIndex (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  ∀ (L : IntermediateField F (maxAbelianSubext F F')) [FiniteDimensional F L] [Normal F L],
    (normGroup F ↥L).index = Module.finrank F ↥L

/-- **The kernel condition**: there is a single homomorphism `Fˣ →* Gal(F^{ab}/F)` whose
restriction to every finite abelian Galois level has kernel exactly the norm group.

Unlike `ReciprocityMap` it does *not* ask for surjectivity; that is recovered from `NormIndex` by
counting (both the norm quotient and the level Galois group have `[L:F]` elements). -/
structure KernelCondition (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] where
  /-- the homomorphism `Fˣ →* Gal(F^{ab}/F)`. -/
  artin : Fˣ →* AbGal F F'
  /-- its level kernels are the norm groups. -/
  ker_level : ∀ (L : IntermediateField F (maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L] (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      MonoidHom.ker ((levelRestrict L).comp artin) = normGroup F ↥L

namespace ReciprocityMap

variable (R : ReciprocityMap F F')

/-- **The Artin map at a finite abelian level**, `Fˣ ⧸ N_{L/F} Lˣ →* Gal(L/F)`: the map induced by
`R.artin` on the quotient by the norm group. -/
noncomputable def artinLevelHom (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    (Fˣ ⧸ normGroup F ↥L) →* (↥L ≃ₐ[F] ↥L) :=
  QuotientGroup.lift (normGroup F ↥L) ((levelRestrict L).comp R.artin)
    (by rw [(R.isLevelIso L hcomm).2])

/-- The level Artin map is induced by `R.artin` on representatives. -/
theorem artinLevelHom_mk (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) (x : Fˣ) :
    R.artinLevelHom L hcomm (QuotientGroup.mk x) = (levelRestrict L) (R.artin x) :=
  QuotientGroup.lift_mk' _ _ x

theorem artinLevelHom_surjective (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    Function.Surjective (R.artinLevelHom L hcomm) := by
  intro g
  obtain ⟨x, hx⟩ := (R.isLevelIso L hcomm).1 g
  exact ⟨QuotientGroup.mk x, by rw [artinLevelHom_mk]; exact hx⟩

theorem artinLevelHom_injective (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    Function.Injective (R.artinLevelHom L hcomm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := normGroup F ↥L) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := normGroup F ↥L) b
  rw [artinLevelHom_mk, artinLevelHom_mk] at hab
  have hmem : x * y⁻¹ ∈ MonoidHom.ker ((levelRestrict L).comp R.artin) := by
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_inv, hab, mul_inv_cancel]
  rw [(R.isLevelIso L hcomm).2] at hmem
  exact (QuotientGroup.eq).mpr (by simpa [mul_comm] using inv_mem hmem)

/-- **The reciprocity isomorphism at a finite abelian level**: `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`. -/
noncomputable def artinLevelMulEquiv (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    (Fˣ ⧸ normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L) :=
  MulEquiv.ofBijective (R.artinLevelHom L hcomm)
    ⟨R.artinLevelHom_injective L hcomm, R.artinLevelHom_surjective L hcomm⟩

/-- The reciprocity isomorphism at a level is the map induced by the Artin map. -/
theorem artinLevelMulEquiv_mk (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) (x : Fˣ) :
    ((R.artinLevelMulEquiv L hcomm) (QuotientGroup.mk x) : ↥L ≃ₐ[F] ↥L) =
      (levelRestrict L) (R.artin x) :=
  R.artinLevelHom_mk L hcomm x

include R in
/-- A `ReciprocityMap` gives the `KernelCondition` (forgetting surjectivity). -/
def toKernelCondition : KernelCondition F F' where
  artin := R.artin
  ker_level L hfd hnorm hcomm := (R.isLevelIso L hcomm).2

include R in
/-- **The norm index theorem follows from the reciprocity law**: the level isomorphism
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` identifies the index of the norm group with the order of
`Gal(L/F)`, which is `[L : F]`. -/
theorem normIndex : NormIndex F F' := by
  intro L hfd hnorm
  haveI : FiniteDimensional F L := hfd
  haveI : Normal F L := hnorm
  rw [Subgroup.index_eq_card,
    ← IsGalois.card_aut_eq_finrank F ↥L]
  exact Nat.card_congr
    (R.artinLevelMulEquiv L (NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal L)).toEquiv

include R in
/-- **The reciprocity map is the `ArtinReciprocity` datum with the existence theorem as the only
missing field.** -/
def toArtinReciprocity (hex : ExistenceTheorem F F') : NK.LocalCFT.ArtinReciprocity F F' where
  artin := R.artin
  isLevelIso := R.isLevelIso
  cofinal := hex

end ReciprocityMap

/-- An `ArtinReciprocity` datum is in particular a `ReciprocityMap`. -/
def _root_.NK.LocalCFT.ArtinReciprocity.toReciprocityMap
    (D : NK.LocalCFT.ArtinReciprocity F F') : ReciprocityMap F F' where
  artin := D.artin
  isLevelIso := D.isLevelIso

/-- **The residual gives the Artin reciprocity datum.** -/
theorem nonempty_artinReciprocity_of_residual (h : LocalResidual F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') :=
  ⟨(Classical.choice h.reciprocity).toArtinReciprocity h.existence⟩

/-- **The same, from the two classical inputs separately**: the reciprocity law (in single-map
form) and the existence theorem. -/
theorem nonempty_artinReciprocity_of_reciprocityMap (h : Nonempty (ReciprocityMap F F'))
    (hex : ExistenceTheorem F F') : Nonempty (NK.LocalCFT.ArtinReciprocity F F') :=
  ⟨(Classical.choice h).toArtinReciprocity hex⟩

/-- **The Artin reciprocity datum is equivalent to the residual**: an
`ArtinReciprocity F F'` is precisely a `ReciprocityMap` whose norm groups are cofinal, so the
residual is not weaker than the datum in content — it is the datum split into its two classical
halves. -/
theorem nonempty_artinReciprocity_iff_residual (hex : ExistenceTheorem F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') ↔ Nonempty (ReciprocityMap F F') :=
  ⟨fun h => ⟨(Classical.choice h).toReciprocityMap⟩,
    fun h => nonempty_artinReciprocity_of_reciprocityMap h hex⟩

end NK.LocalArtin
