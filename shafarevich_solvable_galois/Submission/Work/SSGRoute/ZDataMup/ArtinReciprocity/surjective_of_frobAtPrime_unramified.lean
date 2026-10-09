import Mathlib
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-- **A Frobenius-normalised map out of the idèles of an abelian extension is surjective.**

Cheap route (reuse, as in `Work.SSGRoute.ZDataMup.localFactor_ramified_eq_one`): the range of `Φ`
contains `frobAtPrime Q` for every unramified `Q` by `hfrob`, so it contains all Frobenius elements;
Frobenius generation for abelian `L/K` (`NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem`,
instantiated at the finite set `NK.CFTLib.ExistsCongruence.ramPrimes`, whose defining property
`ramificationIdx_eq_one_of_notMem_ramPrimes` says primes outside it are unramified) gives
`Φ.range = ⊤`.  The final step is
`(NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ).mp hσ`,
with `hunr := isUnramifiedIn_of_ramificationIdxIn_eq_one` from the `ramPrimes` property.

Second use: with this lemma, `hfrob` for `M/K` yields commutativity of `Gal(M/K)` (the range of the
abelian `𝕀 K` contains all Frobenius elements), which is what the remaining `sorry` in
`productFormula_descent`'s clause 3 needs. -/
theorem surjective_of_frobAtPrime_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :
    Function.Surjective Φ := by
  classical
  -- `Φ` is surjective as soon as its range is everything; we show the range is a subgroup
  -- containing every Frobenius at a prime outside the finite set `ramPrimes`.
  rw [← MonoidHom.range_eq_top]
  refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L)
    (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)) Φ.range ?_
  intro p hp σ hσ
  -- A prime outside `ramPrimes` is unramified in `L/K`, by definition of `ramPrimes`.
  have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := fun q hq =>
    NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes (K := K) (L := L) hp hq
  -- At an unramified prime the Frobenius is unique, so `σ` is the chosen `frobAtPrime p`.
  rw [NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ] at hσ
  exact ⟨NK.HeckeL.ideleOfPrime K p, by rw [hfrob p hunr, hσ]⟩

end Work.SSGRoute.ZDataMup.ArtinReciprocity
