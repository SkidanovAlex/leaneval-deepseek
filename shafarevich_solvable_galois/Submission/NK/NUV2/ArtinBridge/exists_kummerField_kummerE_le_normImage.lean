import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.NormIndex.GaloisCase
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.NUV2.ArtinBridge.pow_mem_normGroup_of_exponent
import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
import Submission.NK.NUV2.ArtinBridge.KummerSUnitFieldInfinite
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ArtinBridge.finrank_kummerSUnitField
import Submission.NK.NUV2.ArtinBridge.finiteDimensional_kummerSUnitField
import Submission.NK.NUV2.ArtinBridge.ramificationIdx_eq_one_kummerSUnitField
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-- Existence of a Kummer field of degree `p ^ |S|` whose norm group contains Milne's `E`; the
separable closure used to realise the field is a variable, so that all the instances are those of
the ambient context. -/
theorem exists_kummerField_kummerE_le_normImage_aux {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {p : ℕ}
    (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Module.finrank K L = p ^ S.card ∧
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
          NK.GlobalCFT.Idele.normImage K L := by
  haveI hfd : FiniteDimensional K ↥(kummerSUnitField K Ω p S) :=
    finiteDimensional_kummerSUnitField (K := K) (Ω := Ω) hp hζ S hSinf
  haveI hnf : NumberField ↥(kummerSUnitField K Ω p S) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  have hgal : IsGalois K ↥(kummerSUnitField K Ω p S) :=
    isGalois_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p) hp hζ
  have hcomm : IsMulCommutative
      (↥(kummerSUnitField K Ω p S) ≃ₐ[K] ↥(kummerSUnitField K Ω p S)) :=
    isMulCommutative_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p) hp hζ
  have hexp : ∀ σ : ↥(kummerSUnitField K Ω p S) ≃ₐ[K] ↥(kummerSUnitField K Ω p S),
      σ ^ p = 1 :=
    pow_algEquiv_eq_one_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p) hp hζ
  have hdeg : Module.finrank K ↥(kummerSUnitField K Ω p S) = p ^ S.card :=
    finrank_kummerSUnitField (K := K) (Ω := Ω) hp hζ S hSinf
  have hInf : ∀ (v : NumberField.InfinitePlace K)
      (w : NumberField.InfinitePlace ↥(kummerSUnitField K Ω p S)) [w.LiesOver v],
      ∀ x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
        (NK.GlobalCFT.Place.ofInfinite v),
      ∃ u : w.Completionˣ, NK.GlobalCFT.Place.localNormInfinite w v u = x :=
    fun v w _ x hx => localPow_mem_localNormInfinite_kummerSUnitField (K := K) (Ω := Ω)
      hp hζ S v w x hx
  have hram : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ q : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers ↥(kummerSUnitField K Ω p S)),
        q.asIdeal.LiesOver Q.asIdeal ∧
          q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) →
      NK.GlobalCFT.Place.ofFinite Q ∈ S := by
    intro Q hQ
    by_contra hQS
    obtain ⟨q, hq, hram'⟩ := hQ
    exact hram' (ramificationIdx_eq_one_kummerSUnitField (K := K) (Ω := Ω) hp hζ S hSinf
      hSp Q hQS q hq)
  have hle : NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
      NK.GlobalCFT.Idele.normImage K ↥(kummerSUnitField K Ω p S) :=
    kummerE_le_normImage_of_isGalois_exp (K := K) (L := ↥(kummerSUnitField K Ω p S))
      hp hexp S hSinf hram hInf
  exact ⟨↥(kummerSUnitField K Ω p S), inferInstance, hnf, inferInstance, hfd, hgal, hcomm,
    hdeg, hle⟩

theorem exists_kummerField_kummerE_le_normImage {K : Type} [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Module.finrank K L = p ^ S.card ∧
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
          NK.GlobalCFT.Idele.normImage K L :=
  exists_kummerField_kummerE_le_normImage_aux (Ω := SeparableClosure K) hp hζ S hSinf hSp

end NK.NUV2.ArtinBridge
