import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The range of the local algebra map `K_v → L_w` at a real place `v`

If `v` is a real infinite place of `K`, so that `K_v ≅ ℝ` via the real extension embedding
`extensionEmbeddingOfIsReal hv`, and `w` lies over `v`, then the local algebra map
`completionMap : K_v →+* L_w` identifies `K_v` with a closed subfield of `L_w`.  Its image is
exactly the "real locus" of `L_w`:  the elements `y` whose image under the complex extension
embedding `extensionEmbedding w : L_w →+* ℂ` is real.

This holds whatever the type of `w` (real or complex), and it is the archimedean input to the
computation of the local fixed field of the decomposition group.
-/

open scoped NumberField.LiesOver

namespace NK.GlobalCFT.Galois

/-- If `v` is a real place, the local algebra map `K_v →+* L_w` is compatible with the extension
embeddings into `ℂ`. -/
private lemma completionMap_extensionEmbedding_aux {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {v : NumberField.InfinitePlace K}
    {w : NumberField.InfinitePlace L} [w.LiesOver v] (hv : v.IsReal) (a : v.Completion) :
    NumberField.InfinitePlace.Completion.extensionEmbedding w
        (NumberField.LiesOver.completionMap (v := v) (w := w) a)
      = NumberField.InfinitePlace.Completion.extensionEmbedding v a := by
  have h := (NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv).over
  have h2 : ⇑(algebraMap v.Completion w.Completion)
      = ⇑(NumberField.LiesOver.completionMap (v := v) (w := w)) := by
    rw [RingHom.algebraMap_toAlgebra]
  simpa [RingHom.comp_apply, h2] using congrFun (congrArg DFunLike.coe h) a

theorem range_completionMap_of_isReal_under {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {v : NumberField.InfinitePlace K}
    {w : NumberField.InfinitePlace L} [w.LiesOver v] (hv : v.IsReal) :
    Set.range (NumberField.LiesOver.completionMap (v := v) (w := w))
      = {y : w.Completion |
          (NumberField.InfinitePlace.Completion.extensionEmbedding w y).im = 0} := by
  have key : ∀ a : v.Completion,
      NumberField.InfinitePlace.Completion.extensionEmbedding w
        (NumberField.LiesOver.completionMap (v := v) (w := w) a)
      = NumberField.InfinitePlace.Completion.extensionEmbedding v a :=
    completionMap_extensionEmbedding_aux hv
  ext y
  rw [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl⟩
    rw [key x, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv x]
    exact Complex.ofReal_im _
  · intro hy
    have hre : NumberField.InfinitePlace.Completion.extensionEmbedding w y
        = ((NumberField.InfinitePlace.Completion.extensionEmbedding w y).re : ℂ) := by
      apply Complex.ext <;> simp [hy]
    obtain ⟨x, hx⟩ :=
      NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv
        (NumberField.InfinitePlace.Completion.extensionEmbedding w y).re
    refine ⟨x, ?_⟩
    apply (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).injective
    rw [key x, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv x,
      hx]
    exact hre.symm

end NK.GlobalCFT.Galois
