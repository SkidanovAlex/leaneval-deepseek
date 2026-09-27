import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.mesh_sdIterLC
import Submission.Work.Cohomology.exists_delta_affineSimplex
import Submission.Work.Cohomology.sdChainMapIter_gen
import Submission.Work.Cohomology.toChain_apply

/-!
# A high enough iterate of the subdivision operator refines an open cover

Let `U, V ⊆ X` be an open cover of a topological space and `σ` a singular `n`-simplex of `X`.
The small-simplices theorem needs the elementary fact that some iterate `sdChainMapIter X N` of the
barycentric subdivision chain map takes the generator `gen X n σ` into the small chains: the
subdivision is *metric*, its simplices shrink with the mesh bound `(n/(n+1))^N`
(`Work.Cohomology.mesh_sdIterLC`), and below the Lebesgue number of the pullback cover of `Δⁿ`
(`Work.Cohomology.exists_delta_affineSimplex`) every subdivided simplex lies in `U` or in `V`.

## Main result

* `exists_iter_small` — some iterate of the subdivision sends every singular simplex into the
  small chains of an open cover.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The image of the push-forward of an affine simplex along `f` is the range of `f` on the
underlying affine simplex.  Concretely, the singular `n`-simplex
`(TopCat.toSSet.map f).app _ (linSimplex v)` of `X` has underlying map `affineSimplex v ≫ f`. -/
lemma range_sdMap_toSSet_map_linSimplex {X : TopCat} (n : ℕ) (f : Delta n ⟶ X)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) :
    Set.range (fun z : (Delta n : TopCat) =>
      sdMap n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) (linSimplex v)) z)
      = Set.range (fun z : (Delta n : TopCat) => f (affineSimplex v z)) := by
  have hz : ∀ z : (Delta n : TopCat),
      sdMap n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) (linSimplex v)) z
        = f (affineSimplex v z) := by
    intro z
    rw [sdMap_map]
    simp only [sdMap_linSimplex]
    rfl
  rw [funext hz]

/-- **Pushing an affine simplex of the subdivision forward.**  If the segment of `f` realizing the
affine simplex with vertices `v` lies in `U` or in `V`, then the push-forward of the generator
`linSimplex v` is a small chain. -/
lemma isSmallChain_pushChain_gen_linSimplex {X : TopCat} {U V : Set X} (n : ℕ)
    (f : Delta n ⟶ X) (δ : ℝ)
    (hδ : ∀ v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)), meshVF v < δ →
      (Set.range (fun z : (Delta n : TopCat) => f (affineSimplex v z)) ⊆ U ∨
       Set.range (fun z : (Delta n : TopCat) => f (affineSimplex v z)) ⊆ V))
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) (hv : meshVF v < δ) :
    IsSmallChain U V (pushChain (Delta n) X f n (gen (Delta n) n (linSimplex v))) := by
  rw [pushChain_gen]
  apply isSmallChain_gen
  rw [isSmall_iff]
  rw [range_sdMap_toSSet_map_linSimplex n f v]
  exact hδ v hv

/-- **A high enough iterate of the subdivision lands in the small chains.**  For an open cover
`X = U ∪ V` and a singular `n`-simplex `σ` there is `N` such that the `N`-fold subdivision of the
generator `gen X n σ` is a small chain. -/
theorem exists_iter_small {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) (σ : Simplex X n) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n (gen X n σ)) := by
  -- the Lebesgue number of the pullback cover of `Δⁿ`
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_affineSimplex U V hU hV hUV n σ
  -- the mesh of the `N`-fold subdivided simplex is `(n/(n+1))^N`, which tends to `0`
  have hlt : ((n : ℝ) / (n + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδpos hlt
  refine ⟨N, ?_⟩
  rw [sdChainMapIter_gen X n N σ]
  rw [toChain_apply]
  rw [map_sum]
  refine IsSmallChain.sum _ _ fun v hv => ?_
  rw [map_zsmul]
  refine IsSmallChain.smul _ ?_
  refine isSmallChain_pushChain_gen_linSimplex n (sdMap n σ) δ (fun v hv => hδ n v hv) v ?_
  exact lt_of_le_of_lt (mesh_sdIterLC n N v hv) hN

end

end Work.Cohomology
