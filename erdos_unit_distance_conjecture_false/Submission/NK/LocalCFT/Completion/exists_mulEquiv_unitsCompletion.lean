import Mathlib
import Submission.NK.LocalCFT.Basic

/-!
# The infinite-level reciprocity isomorphism `Fˣ^{∧} ≃* G_F^{ab}`

`NK.LocalCFT.ArtinReciprocity F F'` is the (corrected) local reciprocity datum: a single
homomorphism `artin : Fˣ →* Gal(F^{ab}/F)` whose composite with the restriction
`Gal(F^{ab}/F) →* Gal(L/F)` to every finite abelian Galois level `L ≤ F^{ab}` is surjective with
kernel the norm group `N_{L/F} Lˣ`, and whose norm groups are cofinal among the finite-index
subgroups of `Fˣ`.

The content of this file is that such a datum *is* the infinite-level reciprocity isomorphism:
gluing the level isomorphisms along the (automatically compatible) restrictions, the Artin map
induces an isomorphism

`Fˣ^{∧} ≃* Gal(F^{ab}/F) = G_F^{ab}`

from the profinite completion of the unit group of `F` onto the abelianised absolute Galois
group.  Surjectivity comes from surjectivity at every finite level, injectivity from the
cofinality of the norm groups.

## Route

Rather than repeating the (substantial) limit construction, we observe that the datum
`ArtinReciprocity F F'` is *literally* a `LocalReciprocityDatum F F^{ab}` for the maximal abelian
subextension `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`:

* its `artin` already lands in `Gal(F^{ab}/F)`, which is the absolute Galois group of `F^{ab}`;
* the restriction maps `levelRestrict L` of `NK.LocalCFT.Basic` are by definition
  `AlgEquiv.restrictNormalHom` of the level, which is what `LocalReciprocityDatum.isLevelIso`
  uses;
* the cofinality axiom is the same statement.

The infinite-level reciprocity theorem
`NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian` — already proved in the workspace —
applied to this datum over the extension `F^{ab}/F` gives the isomorphism
`Fˣ^{∧} ≃* Gal(M/F)`, where `M = maxAbelianSubext F F^{ab}` is the maximal abelian
subextension of `F^{ab}/F`.  Since `Gal(F^{ab}/F)` is abelian, `M = F^{ab}`
(`maxAbelianSubext_maxAbelianSubext`), so `Gal(M/F) = Gal(F^{ab}/F) = G_F^{ab}` and the statement
follows.
-/

open scoped Classical

-- The instances below are genuinely local (they are supplied to `AlgEquiv.restrictNormalHom`
-- and to the infinite-level reciprocity theorem); the style linter cannot see that.
set_option linter.style.haveILetI false

namespace NK.LocalCFT.Completion

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **An abelian Galois extension is its own maximal abelian subextension.**  If the commutator
subgroup of `Gal(A/F)` is trivial then the fixed field of that commutator subgroup — the maximal
abelian subextension of `A/F` — is all of `A` (`IntermediateField.fixedField_bot`). -/
theorem maxAbelianSubext_eq_top_of_commutator_eq_bot {A : Type v} [Field A] [Algebra F A]
    (h : commutator (A ≃ₐ[F] A) = ⊥) :
    NK.LocalReciprocity.maxAbelianSubext F A = ⊤ := by
  rw [NK.LocalReciprocity.maxAbelianSubext, h, IntermediateField.fixedField_bot]

/-- **`F^{ab}` is its own maximal abelian subextension**, because `Gal(F^{ab}/F)` is abelian
(`NK.LocalReciprocity.commutator_gal_maxAbelianSubext`). -/
theorem maxAbelianSubext_maxAbelianSubext :
    NK.LocalReciprocity.maxAbelianSubext F ↥(NK.LocalReciprocity.maxAbelianSubext F F') = ⊤ :=
  maxAbelianSubext_eq_top_of_commutator_eq_bot (A := ↥(NK.LocalReciprocity.maxAbelianSubext F F'))
    NK.LocalReciprocity.commutator_gal_maxAbelianSubext

/-- The `F`-algebra isomorphism between `F^{ab}` and the maximal abelian subextension of
`F^{ab}/F`, which is itself (`maxAbelianSubext_maxAbelianSubext`). -/
noncomputable def maxAbelianSubextSelfAlgEquiv :
    ↥(NK.LocalReciprocity.maxAbelianSubext F ↥(NK.LocalReciprocity.maxAbelianSubext F F')) ≃ₐ[F]
      ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
  (IntermediateField.equivOfEq maxAbelianSubext_maxAbelianSubext).trans
    IntermediateField.topEquiv

/-- **The Artin reciprocity datum on `F^{ab}` is a reciprocity datum in the sense of
`NK.LocalReciprocity`.**  The fields of the two structures agree verbatim: the Artin map of
`D` already takes values in `Gal(F^{ab}/F)`, and the restriction maps of
`NK.LocalCFT.Basic` are `AlgEquiv.restrictNormalHom`, exactly as in
`NK.LocalReciprocity.LocalReciprocityDatum`. -/
noncomputable def artinReciprocityToDatum (D : NK.LocalCFT.ArtinReciprocity F F') :
    NK.LocalReciprocity.LocalReciprocityDatum F ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
  { artin := D.artin
    isLevelIso := fun L _ _ hcomm => D.isLevelIso L hcomm
    cofinal := D.cofinal }

/-- **Infinite-level local reciprocity from an Artin reciprocity datum**: the profinite
completion of `Fˣ` is the abelianised absolute Galois group `G_F^{ab} = Gal(F^{ab}/F)`.

The Artin map `D.artin` is the limit of its level isomorphisms
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, which are automatically compatible with the restriction maps of
the levels; passing to the limit over all finite-index normal subgroups of `Fˣ` (the definition of
the profinite completion) and over all finite abelian Galois levels of `F^{ab}/F` (the definition
of `Gal(F^{ab}/F)`) yields the isomorphism. -/
theorem exists_mulEquiv_unitsCompletion {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') :
    Nonempty (NK.LocalReciprocity.completionUnits F ≃* NK.LocalCFT.AbGal F F') := by
  haveI : IsGalois F ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
    NK.LocalReciprocity.instIsGaloisMaxAbelianSubext
  obtain ⟨Φ⟩ := NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian
    (artinReciprocityToDatum D)
  exact ⟨Φ.trans (maxAbelianSubextSelfAlgEquiv (F := F) (F' := F')).autCongr⟩

end NK.LocalCFT.Completion
