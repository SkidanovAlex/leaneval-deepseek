import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.IdeleClassGroup

/-- **The nonarchimedean annulus is compact.** For a nonarchimedean place `q` of a number field
`K` and a positive constant `C`, the set of units `y` of the `q`-adic completion with
`C⁻¹ ≤ ‖y‖ ≤ 1` is compact.

Suggested route: the set `S := {x : K_q | C⁻¹ ≤ ‖x‖ ≤ 1}` is closed (`‖·‖` is continuous) and, by
`Valued.toNormedField.norm_le_one_iff`, contained in the valuation ring `q.adicCompletionIntegers K`,
which is compact (`Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers`);
hence `S` is compact as a closed subset of a compact set (`IsCompact.of_isClosed_subset`).
Since `C⁻¹ > 0`, `0 ∉ S`, so every element of `S` is a unit and `S` is the image of
`{y : K_qˣ | C⁻¹ ≤ ‖y‖ ≤ 1}` under `Units.val`; compactness transfers along the topological
embedding `Units.isEmbedding_val₀` (used in the same way in
`Submission/Work/GlobalCFT/LocalField/globalCFT_localUnits_isCompact_finite.lean`). -/
theorem isCompact_annulus_finite {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {C : ℝ} (hC : 0 < C) :
    IsCompact {y : (q.adicCompletion K)ˣ |
      C⁻¹ ≤ ‖(y : q.adicCompletion K)‖ ∧ ‖(y : q.adicCompletion K)‖ ≤ 1} := by
  -- The valuation ring `𝒪_q` is compact as a subset of `K_q`.
  have hInt : IsCompact ((q.adicCompletionIntegers K) : Set (q.adicCompletion K)) := by
    have := Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K q
    have h := (isCompact_univ (X := (q.adicCompletionIntegers K))).image
      (continuous_subtype_val : Continuous (Subtype.val :
        (q.adicCompletionIntegers K) → q.adicCompletion K))
    rwa [Set.image_univ, Subtype.range_coe] at h
  -- The annulus `{x : K_q | C⁻¹ ≤ ‖x‖ ≤ 1}` is closed.
  have hclosed : IsClosed {x : q.adicCompletion K | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    rw [Set.ofPred_and]
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  -- ... and it is contained in `𝒪_q`.
  have hsub : {x : q.adicCompletion K | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ⊆
      ((q.adicCompletionIntegers K) : Set (q.adicCompletion K)) := by
    intro x hx
    rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    exact hx.2
  have hA : IsCompact {x : q.adicCompletion K | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
    IsCompact.of_isClosed_subset hInt hclosed hsub
  -- Every element of the annulus is nonzero, hence a unit.
  have hrange : {x : q.adicCompletion K | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ⊆
      Set.range (Units.val : (q.adicCompletion K)ˣ → q.adicCompletion K) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      have : ‖x‖ = 0 := by rw [h, norm_zero]
      have hpos : 0 < C⁻¹ := inv_pos.mpr hC
      linarith [hx.1]
    exact ⟨Units.mk0 x hx0, rfl⟩
  have hpre : {y : (q.adicCompletion K)ˣ |
      C⁻¹ ≤ ‖(y : q.adicCompletion K)‖ ∧ ‖(y : q.adicCompletion K)‖ ≤ 1} =
      (Units.val : (q.adicCompletion K)ˣ → q.adicCompletion K) ⁻¹'
        {x : q.adicCompletion K | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := rfl
  -- Compactness transfers along the topological embedding `Units.val`.
  rw [hpre]
  exact (Units.isEmbedding_val₀ (G₀ := q.adicCompletion K)).isInducing.isCompact_preimage' hA
    hrange

end NK.GlobalCFT.IdeleClassGroup
