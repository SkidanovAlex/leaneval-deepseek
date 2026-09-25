import Mathlib
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.NK.LocalReciprocity.Frobenius
import Submission.NK.LocalReciprocity.ArtinUnramified
import Submission.NK.LocalReciprocity.localRestrict_frobeniusLocal

namespace NK.LocalReciprocity

/-- **Restriction compatibility of the canonical unramified Artin maps.**

For a tower `K ⊆ L ⊆ M` of number fields (`M/K` finite Galois, `L/K` normal) and places
`w | w|_L | p`, all unramified over `p`, the canonical Frobenius-normalised Artin maps of the
local fields are compatible with the restriction maps `Submission.NeukirchUchida.Local.localRestrict`:
both sides are the group homomorphisms `K_pˣ →* Gal(L_{w|_L}/K_p)` obtained by pushing the
Frobenius through the exponent `valExponent K p`.

This is the *first functoriality* of the local Artin map, and it is what makes the unramified
Artin maps of the levels of a local field into a compatible family (i.e. into a restriction of a
single map `K_pˣ → Gal(K̄_p/K_p)^{ab}`). -/
theorem localRestrict_artinUnramified {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    [hw : w.asIdeal.LiesOver p.asIdeal]
    [hwL : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal.LiesOver p.asIdeal]
    (hunrM : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hunrL : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) = 1)
    (x : (p.adicCompletion K)ˣ) :
    Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
        (NK.LocalReciprocity.artinUnramified p w hunrM x) =
      NK.LocalReciprocity.artinUnramified p
        (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) hunrL x := by
  -- Both `artinUnramified` maps have the same exponent `valExponent K p x`, and `localRestrict` is a
  -- monoid homomorphism carrying the Frobenius of `M_w` to the Frobenius of `L_{w|_L}`
  -- (`NK.LocalReciprocity.localRestrict_frobeniusLocal`).
  -- (`erw` rather than `rw`: the `K_p`-algebra instances of
  -- `NK.LocalReciprocity.instAlgebraAdicCompletion` and
  -- `Submission.NeukirchUchida.Local.adicCompletionAlgebra` are definitionally equal but not
  -- syntactically identical, so rewriting needs full transparency.)
  erw [NK.LocalReciprocity.artinUnramified_apply, NK.LocalReciprocity.artinUnramified_apply,
    map_zpow, NK.LocalReciprocity.localRestrict_frobeniusLocal]
  rfl

end NK.LocalReciprocity
