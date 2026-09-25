import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers

namespace NK.GlobalCFT.LocalField

open NumberField

/-- The group of local units `𝒪_qˣ` at a finite place `q` of a number field `K` is compact: it is
the "sphere" `{x : K_q | v x = 1}` inside the compact valuation ring `𝒪_q`.

The sphere is closed in `K_q` because `v` is continuous, and it is contained in the compact ring
`𝒪_q`, hence compact; it is the image of `𝒪_qˣ` under the topological embedding
`Units.val : K_qˣ → K_q`. -/
theorem globalCFT_localUnits_isCompact_finite {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsCompact ((NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q) :
      Set ((q.adicCompletion K)ˣ))) := by
  have : CompactSpace (q.adicCompletionIntegers K) :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K q
  -- `𝒪_qˣ` is the preimage under `Units.val` of the "sphere" `{v = 1}` of `K_q`.
  have hS : ((NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q) :
        Set ((q.adicCompletion K)ˣ))) =
      (Units.val : (q.adicCompletion K)ˣ → q.adicCompletion K) ⁻¹'
        {x : q.adicCompletion K | Valued.v.restrict x = 1} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one,
      Valuation.restrict_eq_one_iff]
  -- the ring of integers `𝒪_q` is compact as a subset of `K_q`
  have hInt : IsCompact ((q.adicCompletionIntegers K) : Set (q.adicCompletion K)) := by
    have h := (isCompact_univ (X := (q.adicCompletionIntegers K))).image
      (continuous_subtype_val : Continuous (Subtype.val :
        (q.adicCompletionIntegers K) → q.adicCompletion K))
    rwa [Set.image_univ, Subtype.range_coe] at h
  -- the sphere `{v = 1}` is closed and sits inside `𝒪_q`, hence is compact
  have hA : IsCompact {x : q.adicCompletion K | Valued.v.restrict x = 1} := by
    refine IsCompact.of_isClosed_subset hInt (Valued.isClosed_sphere (q.adicCompletion K) 1) ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valuation.restrict_le_one_iff]
    exact le_of_eq hx
  -- every element of the sphere is a unit
  have hrange : {x : q.adicCompletion K | Valued.v.restrict x = 1} ⊆
      Set.range (Units.val : (q.adicCompletion K)ˣ → q.adicCompletion K) := by
    intro x hx
    have hx' : x ≠ 0 := by
      intro hx0
      rw [Set.mem_ofPred_eq, hx0, map_zero] at hx
      exact one_ne_zero hx.symm
    exact ⟨Units.mk0 x hx', rfl⟩
  rw [hS]
  exact (Units.isEmbedding_val₀ (G₀ := q.adicCompletion K)).isInducing.isCompact_preimage' hA hrange

end NK.GlobalCFT.LocalField
