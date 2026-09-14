import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

open scoped NumberField Valued WithZero
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

noncomputable section

/-- The valuation ring of the `v`-adic completion is complete: it is a closed subset
(`{x | v x ≤ 1}`) of the complete ambient field `v.adicCompletion K`. -/
lemma completeSpace_adicCompletionIntegers (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (Valued.integer (v.adicCompletion K)) := by
  rw [completeSpace_iff_isComplete_range
    (f := (Subtype.val : Valued.integer (v.adicCompletion K) → v.adicCompletion K))
    (isUniformEmbedding_subtype_val.isUniformInducing)]
  have hset : Set.range (fun y : Valued.integer (v.adicCompletion K) ↦ (y : v.adicCompletion K))
      = {x : v.adicCompletion K | Valued.v x ≤ 1} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hset]
  exact (Valued.isClosed_integer (R := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)).isComplete

/-- The valuation ring of the `v`-adic completion is a discrete valuation ring. -/
lemma isDiscreteValuationRing_adicCompletionIntegers (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) := by
  change IsDiscreteValuationRing (v.adicCompletionIntegers K)
  infer_instance

/-- The residue field of the `v`-adic completion is finite (it is isomorphic to
the finite residue field `𝓞 K ⧸ v.asIdeal` of the prime `v`). -/
lemma finite_residueField_adicCompletion (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
  classical
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := K) v
  haveI hfin : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal) e.symm.toEquiv

/-- The ring of integers of the `v`-adic completion of a number field `K` is compact. -/
theorem compactSpace_adicCompletionIntegers (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompactSpace (v.adicCompletionIntegers K) := by
  change CompactSpace (Valued.integer (v.adicCompletion K))
  have hc : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    completeSpace_adicCompletionIntegers K v
  have hdvr : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    isDiscreteValuationRing_adicCompletionIntegers K v
  have hres : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    finite_residueField_adicCompletion K v
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)).mpr ⟨hc, hdvr, hres⟩

end

end Commons.NumberTheory.NumberField.Completion