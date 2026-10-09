import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.IdeleClassGroup

/-- **The archimedean annulus is compact.** For an infinite place `w` of a number field `K` and a
positive constant `C`, the set of units `z` of the completion `K_w` with `C⁻¹ ≤ ‖z‖ ≤ C` is
compact. Suggested route: `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`
says the embedding `K_w →+* ℂ` is an isometry, hence a closed embedding into the complete space
`ℂ`; the annulus in `ℂ` is closed and bounded hence compact, and preimages of compact sets under
closed embeddings are compact (`Topology.IsClosedEmbedding.isCompact_preimage`); finally transfer
from `K_w` to `K_wˣ` along the topological embedding `Units.val`
(`Units.isEmbedding_val₀`, which needs `ContinuousInv₀`). Every element of the annulus is nonzero
since `C⁻¹ > 0`. -/
theorem isCompact_annulus_infinite {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) {C : ℝ} (hC : 0 < C) :
    IsCompact {z : w.Completionˣ | C⁻¹ ≤ ‖(z : w.Completion)‖ ∧ ‖(z : w.Completion)‖ ≤ C} := by
  -- The extended embedding `K_w →+* ℂ` preserves the norm.
  have hnorm : ∀ y : w.Completion,
      ‖NumberField.InfinitePlace.Completion.extensionEmbedding w y‖ = ‖y‖ := by
    intro y
    have h1 : dist (NumberField.InfinitePlace.Completion.extensionEmbedding w y)
        (NumberField.InfinitePlace.Completion.extensionEmbedding w 0) = dist y 0 :=
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq y 0
    rw [map_zero] at h1
    rwa [dist_zero_right, dist_zero_right] at h1
  -- The archimedean annulus in `ℂ` is closed and bounded, hence compact.
  set T : Set ℂ := {s : ℂ | C⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ C} with hT
  have hTc : IsCompact T := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) C) ?_ ?_
    · rw [hT]
      exact isClosed_Icc.preimage continuous_norm
    · intro s hs
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hs.2
  -- The annulus of `K_w` is the preimage of `T` under the closed embedding into `ℂ`.
  have hS : IsCompact (NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹' T) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      hTc
  have hSeq : (NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹' T) =
      {x : w.Completion | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ C} := by
    ext x
    simp only [hT, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hnorm x]
  rw [hSeq] at hS
  -- Every element of the annulus is nonzero, hence a unit.
  have hrange : {x : w.Completion | C⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ C} ⊆
      Set.range (Units.val : w.Completionˣ → w.Completion) := by
    rintro x ⟨h1, _⟩
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      have : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  -- Transfer compactness along the topological embedding `Units.val`.
  have h :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).isInducing.isCompact_preimage' hS hrange
  convert h using 1
  ext z
  simp

end NK.GlobalCFT.IdeleClassGroup
