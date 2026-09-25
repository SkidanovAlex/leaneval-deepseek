import Mathlib
import Submission.NK.NUV2.LC.RouteB.RouteBDeps

/-!
# The place of a subfield induced by a place of a separable closure

Let `K'` be a separable closure of the number field `K`, let `A` be a place of `K'` over a
finite prime of `K`, and let `L ≤ M` be finite Galois intermediate fields.  The place `w_M` of
`M` cut out by `A` (namely `Submission.NeukirchUchida.Local.placeOf`, the finite place whose
valuation ring is `A ∩ M`) lies over the place `w_L` of `L` cut out by `A`, whenever the
valuation ring of `w_L` is `A ∩ L`.

This is the compatibility of the two levels of the projective system of finite places attached
to `A`: the place of the bigger field restricts to the place of the smaller one.  The proof is
that both valuation rings are the intersection of `A` with `L`; comparing the two intersection
computations, the claim reduces to the injectivity of `q ↦ 𝒪_q` on the finite places of a number
field.
-/

set_option linter.style.haveILetI false

open scoped NumberField

namespace NK.NUV2.LC.RouteB

/-- Let `L ≤ M` be finite Galois intermediate fields of a separable closure `K'` of the number
field `K`, and let `q` be the finite place of `L` whose valuation ring is `A ∩ L` for a place `A`
of `K'` over a finite prime of `K`.  Then the place of `M` cut out by the same `A` lies over
`q`. -/
theorem liesOver_placeOf_v2 {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.toIntermediateField))
    (hq : A.1.comap (algebraMap ↥L.toIntermediateField K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L.toIntermediateField q) :
    @NK.GlobalCFT.Place.LiesOver ↥L.toIntermediateField _ _ ↥M.toIntermediateField _ _
      ((IntermediateField.inclusion hLM).toAlgebra)
      (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf
        (NK.HasseTwist.primeUnder A) A.1 (NK.HasseTwist.primeUnder_spec A)
        (M : IntermediateField K K')))
      (NK.GlobalCFT.Place.ofFinite q) := by
  -- the algebra structure of `M` over `L` is the one induced by the inclusion
  letI : Algebra ↥L.toIntermediateField ↥M.toIntermediateField :=
    (IntermediateField.inclusion hLM).toAlgebra
  have hinc : (algebraMap ↥L.toIntermediateField ↥M.toIntermediateField) =
      (IntermediateField.inclusion hLM).toRingHom := rfl
  -- the place of `M` cut out by `A`
  set w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M.toIntermediateField) :=
    Submission.NeukirchUchida.Local.placeOf (NK.HasseTwist.primeUnder A) A.1
      (NK.HasseTwist.primeUnder_spec A) (M : IntermediateField K K') with hw
  -- its defining property
  have hM : A.1.comap (algebraMap ↥M.toIntermediateField K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M.toIntermediateField w := by
    rw [hw]
    exact Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf _ _ _ _
  -- the place of `L` below `w`
  let q' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥L.toIntermediateField) :=
    ⟨Ideal.under (𝓞 ↥L.toIntermediateField) w.asIdeal,
      Ideal.IsPrime.under _ w.asIdeal,
      Ideal.under_ne_bot _ w.ne_bot⟩
  have hQ' : q'.asIdeal = w.asIdeal.under (𝓞 ↥L.toIntermediateField) := rfl
  have hlies : w.asIdeal.LiesOver q'.asIdeal := Ideal.LiesOver.mk rfl
  -- the valuation ring of `w`, restricted to `L`, is the valuation ring of `q'`
  have htower :
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M.toIntermediateField w).comap
          (algebraMap ↥L.toIntermediateField ↥M.toIntermediateField) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L.toIntermediateField q' :=
    Commons.RingTheory.Valuation.comap_valuationSubringAtPrime q' w hlies
  -- ... and it is `A ∩ L`, hence the valuation ring of `q`
  have hchain :
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M.toIntermediateField w).comap
          (algebraMap ↥L.toIntermediateField ↥M.toIntermediateField) =
        A.1.comap (algebraMap ↥L.toIntermediateField K') := by
    rw [hinc, ← hM]
    exact Commons.RingTheory.Valuation.comap_inclusion_comap_eq hLM A.1
  have heq : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L.toIntermediateField q' =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L.toIntermediateField q :=
    htower.symm.trans (hchain.trans hq)
  have hq'q : q' = q := Commons.RingTheory.Valuation.valuationSubringAtPrime_injective heq
  refine NK.GlobalCFT.Place.liesOver_ofFinite ?_
  refine Ideal.LiesOver.mk ?_
  rw [← hQ', ← hq'q]

end NK.NUV2.LC.RouteB
