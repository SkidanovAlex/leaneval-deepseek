import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.NK.NeukirchUchida.LocalGaloisCompletion

/-!
# Auxiliary facts for the decomposition group of a place

Two facts used to compare the decomposition group of a place `A` of a separable closure `K'` of a
number field `K` with the absolute Galois group of the completion.

* `val_eq_of_mem_decompositionGroupOf` : an element of the decomposition group of `A` preserves
  the valuation defined by `A`;
* `completionRingEquiv_adicCompletionToPlaceCompletion` : its continuous extension to the
  completion `placeCompletion A` fixes the image of the `p`-adic completion of `K`.
-/

open scoped Pointwise Valued

namespace NK.NeukirchUchida

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- Elements of the decomposition group of `A` preserve the valuation defined by `A`. -/
theorem val_eq_of_mem_decompositionGroupOf (A : ValuationSubring K')
    {σ : Gal(K'/K)} (hσ : σ ∈ NK.Mine.decompositionGroupOf K K' A) (x : K') :
    A.valuation (σ x) = A.valuation x := by
  refine Commons.RingTheory.Valuation.val_eq_of_algEquiv_of_comap_eq
    (Algebra.IsSeparable.isAlgebraic K K') A σ ?_ x
  have h := (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff A σ).mp hσ
  ext x
  rw [ValuationSubring.mem_comap]
  exact (h x).symm

/-- The continuous extension of a valuation-preserving ring automorphism `σ` of `K'` to the
completion `placeCompletion A` fixes the image of the `p`-adic completion of `K`, provided `σ`
fixes `K`. -/
theorem completionRingEquiv_adicCompletionToPlaceCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : K' ≃+* K')
    (hσ : ∀ x : K', A.valuation (σ x) = A.valuation x)
    (hσK : ∀ c : K, σ (algebraMap K K' c) = algebraMap K K' c)
    (z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) :
    Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (adicCompletionToPlaceCompletion p A hA z) =
      adicCompletionToPlaceCompletion p A hA z := by
  have hcont₁ : Continuous fun z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
      Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (adicCompletionToPlaceCompletion p A hA z) :=
    (Submission.NeukirchUchida.Local.continuous_completionRingEquiv A.valuation σ hσ).comp
      (continuous_adicCompletionToPlaceCompletion p A hA)
  have hcont₂ : Continuous fun z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
      adicCompletionToPlaceCompletion p A hA z :=
    continuous_adicCompletionToPlaceCompletion p A hA
  have hclosed : IsClosed {w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p |
      Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (adicCompletionToPlaceCompletion p A hA w) =
      adicCompletionToPlaceCompletion p A hA w} :=
    isClosed_eq hcont₁ hcont₂
  have hdense : Dense (Set.range (algebraMap K
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p))) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K p
  have hsub : Set.range (algebraMap K
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) ⊆
      {w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p |
        Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
          (adicCompletionToPlaceCompletion p A hA w) =
        adicCompletionToPlaceCompletion p A hA w} := by
    rintro w ⟨c, rfl⟩
    show Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (adicCompletionToPlaceCompletion p A hA
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c)) =
      adicCompletionToPlaceCompletion p A hA
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c)
    rw [adicCompletionToPlaceCompletion_algebraMap p A hA c]
    show Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (((algebraMap K K' c : K') : placeCompletion A)) =
      ((algebraMap K K' c : K') : placeCompletion A)
    rw [Submission.NeukirchUchida.Local.completionRingEquiv_coe]
    rw [hσK c]
  have huniv : Set.univ ⊆ {w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p |
      Submission.NeukirchUchida.Local.completionRingEquiv A.valuation σ hσ
        (adicCompletionToPlaceCompletion p A hA w) =
      adicCompletionToPlaceCompletion p A hA w} := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  exact huniv (Set.mem_univ z)

end

end NK.NeukirchUchida
