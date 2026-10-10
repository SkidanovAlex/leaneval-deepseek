import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm on an archimedean completion is onto the positive reals, on units

For an infinite place `w` of a number field `K`, the completion `w.Completion` is a normed field
isometric to `ℝ` (if `w` is real) or to `ℂ` (if `w` is complex).  In both cases the norm map is
onto the positive reals, and every positive real is the norm of a *unit* (a nonzero element).

This is the local (`w`-component) input for the log-map section used in the divisible-torus
arguments: the archimedean component of an idèle with prescribed logarithms `b w` is a unit of
`w.Completion` of norm `exp (b w)`.

## Implementation

`rcases w.isReal_or_isComplex with h | h`.

* real case: `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal h : w.Completion →+* ℝ`
  is surjective (`…surjective_extensionEmbeddingOfIsReal h`) and an isometry
  (`…isometry_extensionEmbeddingOfIsReal h`), so it suffices to lift `Real.exp c`.
* complex case: analogously with `extensionEmbedding w : w.Completion →+* ℂ`,
  `…surjective_extensionEmbedding_of_isComplex h` and `…isometry_extensionEmbedding w`.

Norm transport uses `Isometry.norm_map_of_map_zero` (the `Isometry` in this pin is *defined* as an
`edist`-preserving function, so it must be applied through that lemma rather than `.dist_eq`).
The lifted element is nonzero because its norm is `Real.exp c > 0`, and is packaged with
`Units.mk0`.
-/

namespace Work.SSGRoute.PTW

theorem norm_completion_infinitePlace_surjective (K : Type) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (c : ℝ) :
    ∃ t : Units (w.Completion), ‖((t : w.Completion))‖ = Real.exp c := by
  rcases w.isReal_or_isComplex with h | h
  · obtain ⟨t, ht⟩ :=
      NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal h (Real.exp c)
    have hnorm : ‖t‖ = Real.exp c := by
      have h1 : ‖NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal h t‖ = ‖t‖ :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero
          (map_zero _) t
      rw [ht, Real.norm_of_nonneg (Real.exp_pos c).le] at h1
      exact h1.symm
    exact ⟨Units.mk0 t (by intro h0; rw [h0, norm_zero] at hnorm; exact Real.exp_ne_zero c hnorm.symm),
      by simpa only [Units.val_mk0] using hnorm⟩
  · obtain ⟨t, ht⟩ :=
      NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex h (Real.exp c)
    have hnorm : ‖t‖ = Real.exp c := by
      have h1 : ‖NumberField.InfinitePlace.Completion.extensionEmbedding w t‖ = ‖t‖ :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) t
      rw [ht, Complex.norm_of_nonneg (Real.exp_pos c).le] at h1
      exact h1.symm
    exact ⟨Units.mk0 t (by intro h0; rw [h0, norm_zero] at hnorm; exact Real.exp_ne_zero c hnorm.symm),
      by simpa only [Units.val_mk0] using hnorm⟩

end Work.SSGRoute.PTW
