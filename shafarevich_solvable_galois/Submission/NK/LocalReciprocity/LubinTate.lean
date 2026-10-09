import Submission.NK.LocalReciprocity.Reciprocity
import Submission.NK.LocalReciprocity.Frobenius
import Submission.NK.LocalReciprocity.ArtinUnramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lubin–Tate / existence input of local class field theory

`NK.LocalReciprocity.Reciprocity.LocalReciprocityDatum` packages the canonical,
restriction-compatible family of local reciprocity isomorphisms
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` — equivalently (by the projective-limit description of
`Gal(F'/F)`) a single Artin homomorphism `Fˣ →* Gal(F'/F)` inducing those isomorphisms on the
finite abelian levels — together with the existence theorem (cofinality of the norm groups).

This file records that this datum is *the* remaining input of the local side of
Neukirch–Uchida, and what is known about it unconditionally:

* On the subfamily of **unramified** extensions the datum is constructed unconditionally in
  `NK.LocalReciprocity.artinUnramified`, and `NK.LocalReciprocity.localRestrict_artinUnramified`
  shows that those Artin maps are the restrictions of one another, i.e. form a compatible family.
* The construction of the datum on all finite abelian extensions is the Lubin–Tate theorem
  (existence of a formal group with a given uniformiser and the explicit reciprocity law), or
  equivalently the existence theorem of local class field theory.  It is stated here as the
  definition `LubinTateInput`; it is *not* proved in this development.

Nothing in this file is proved from a `sorry` or a new axiom: `LubinTateInput` is a `Prop`, and
the theorems of `Reciprocity.lean`, `Invariants.lean` etc. take a `LocalReciprocityDatum` (hence
`LubinTateInput`) as an explicit hypothesis.
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

universe u v

/-- **The Lubin–Tate / existence input**: the existence of the canonical reciprocity datum for the
local field `F` with separable closure `F'`.  This is the main theorem of local class field theory
(Lubin–Tate theory plus the explicit reciprocity law). -/
def LubinTateInput (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] : Prop :=
  Nonempty (LocalReciprocityDatum F F')

/-- The Lubin–Tate input provides the reciprocity datum, hence the canonical reciprocity
isomorphisms at all finite abelian levels (`LocalReciprocityDatum.artinLevelMulEquiv`) and the
infinite-level statement of `NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian`. -/
theorem nonempty_localReciprocityDatum_of_lubinTate {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] (h : LubinTateInput F F') : Nonempty (LocalReciprocityDatum F F') :=
  h

/-- **The unconditionally constructed part of the datum**: for a finite Galois extension of number
fields and a place `q | Q` with `e(q|Q) = 1`, the canonical Frobenius-normalised Artin map of the
unramified local extension, together with its characteristic properties
(`artinUnramified_uniformizer`, `artinUnramified_surjective`, `ker_artinUnramified`). -/
theorem exists_artinUnramified {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∃ Φ : (Q.adicCompletion K)ˣ →* (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      MonoidHom.ker Φ = normGroup (Q.adicCompletion K) (q.adicCompletion L) ∧
      Φ (uniformizerUnit K Q) = frobeniusLocal Q q hunr :=
  ⟨artinUnramified Q q hunr, ker_artinUnramified Q q hunr, artinUnramified_uniformizer Q q hunr⟩

end NK.LocalReciprocity
