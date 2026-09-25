import Submission.NK.NUV2.Wall
import Submission.NK.LocalInputs.Defs

/-!
# Leaves of the place correspondence `NK.NUV2.LCAll0` (orchestrator-owned; do not edit)

All in `Type 0`. Design rule: local Galois group isomorphisms are CONTINUOUS (`≃ₜ*`).
-/

namespace NK.NUV2

open IsDedekindDomain

/-- **Leaf 1 (Neukirch; NSW 12.1.9, hard half).** A closed subgroup of `G_K` that is topologically isomorphic to
the absolute Galois group of a completion of some number field at a finite prime lies in the decomposition group of
a place above a finite prime. -/
def DecompContainment : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    (∃ (L : Type) (_ : Field L) (_ : NumberField L) (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      Nonempty (H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))) →
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      H ≤ Submission.NeukirchUchida.decompositionGroup (K₁ := K) A

/-- **Leaf 5.** The decomposition group of a place above `𝔭` is topologically isomorphic to the absolute Galois
group of the completion. -/
def DecompContinuousIso : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (A : ValuationSubring K'),
    A.comap (algebraMap K K') = HeightOneSpectrum.valuationSubringAtPrime K 𝔭 →
    Nonempty (Submission.NeukirchUchida.decompositionGroup (K₁ := K) A ≃ₜ*
      Gal(SeparableClosure (𝔭.adicCompletion K) / 𝔭.adicCompletion K))

/-- **Leaf 6.** Topologically isomorphic local absolute Galois groups have the same residue characteristic and
the same local degree `[K_𝔭 : ℚ_p]`. -/
def LocalArithInvariants : Prop :=
  ∀ (K₁ K₂ : Type) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
    Nonempty (Gal(SeparableClosure (𝔭.adicCompletion K₁) / 𝔭.adicCompletion K₁) ≃ₜ*
      Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)) →
    ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) =
        ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) ∧
      NK.LocalInputs.localDegree K₁ 𝔭 = NK.LocalInputs.localDegree K₂ 𝔮

/-- **Glue G1 target.** A homeomorphic isomorphism of absolute Galois groups preserves decomposition groups. -/
def PDGAll0 : Prop :=
  ∀ (K₁ K₂ K₁' K₂' : Type) [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁]
    [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)), IsHomeomorph ϕ →
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ

end NK.NUV2
