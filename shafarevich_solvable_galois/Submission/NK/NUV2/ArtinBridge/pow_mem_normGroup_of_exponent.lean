import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p`-th powers of local units are norms, when the Galois group has exponent `p`

Let `F = Q.adicCompletion K` be a `p`-adic field and `E / F` a finite abelian Galois extension
whose Galois group has exponent dividing `p` (hypothesis `hexp : ∀ σ, σ ^ p = 1`).  Then every
`p`-th power of a unit of `F` is a norm from `E`:

  `∀ x : Fˣ, x ^ p ∈ N_{E/F} Eˣ`.

The proof is the local reciprocity theorem in the form
`Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local`: the Artin map
`Φ : Fˣ →* Gal(E/F)` is surjective with kernel `N_{E/F} Eˣ`.  Hence it induces an injective map
`Fˣ ⧸ N_{E/F} Eˣ → Gal(E/F)`, and since the target has exponent dividing `p` the quotient
`Fˣ ⧸ N_{E/F} Eˣ` has exponent dividing `p` as well; that is exactly `x ^ p ∈ N_{E/F} Eˣ`.

(Note that this is *not* the statement `[Fˣ : N] = [E : F] ∣ p`: the local degree may well be
`p ^ k`.  What is used is the group-theoretic conclusion `Fˣ / N ↪ Gal(E/F)`, which is stronger
than the numerical norm index theorem.)
-/

namespace NK.NUV2.ArtinBridge

/-- **`p`-th powers of local units are norms for exponent-`p` abelian local extensions.**

For a finite Galois extension `E` of the `p`-adic field `Q.adicCompletion K` with commutative
Galois group of exponent dividing `p`, every `p`-th power of a unit of `Q.adicCompletion K` lies in
the norm group `N_{E/F} Eˣ`. -/
theorem pow_mem_normGroup_of_exponent {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) [Fact p.Prime]
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    [IsMulCommutative (E ≃ₐ[Q.adicCompletion K] E)]
    (hexp : ∀ σ : E ≃ₐ[Q.adicCompletion K] E, σ ^ p = 1) :
    ∀ x : (Q.adicCompletion K)ˣ,
      x ^ p ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K) E := by
  -- the local Galois group is commutative
  have hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  -- the local Artin map: surjective onto `Gal(E/F)`, with kernel the norm group
  obtain ⟨Φ, _hsurj, hker⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local Q hcomm
  intro x
  -- `Φ` kills the `p`-th powers, since `Gal(E/F)` has exponent dividing `p`
  have hx : Φ (x ^ p) = 1 := by rw [map_pow, hexp]
  have hmem : x ^ p ∈ MonoidHom.ker Φ := (MonoidHom.mem_ker).mpr hx
  rw [hker] at hmem
  simpa only [NK.LocalReciprocity.normGroup] using hmem

end NK.NUV2.ArtinBridge
