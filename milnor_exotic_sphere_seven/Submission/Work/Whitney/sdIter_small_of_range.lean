import Mathlib
import Submission.Work.Cohomology.exists_iter_small

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A high enough iterate of the subdivision refines an open cover of the *image* of a simplex

`Work.Cohomology.exists_iter_small` proves that for an open cover `X = U ∪ V` of the *whole*
space, some iterate of the subdivision sends `gen X n σ` into the small chains `IsSmallChain U V`.
Its proof consumes the hypothesis `U ∪ V = univ` in exactly one place: to know that the pullback
cover of `Δⁿ` by `(sdMap n σ)⁻¹U`, `(sdMap n σ)⁻¹V` covers `Δⁿ` (the input of the Lebesgue-number
lemma `Work.Cohomology.lebesgue_delta_openCover`).

This file records the *localised* form, which is what the cap-adapted cone of the rank-one model
product formula needs (`Submission/Work/Whitney/NOTES_tcmRankOneSusp.md` §2): it is enough that the
image of `σ` itself lies in `U ∪ V`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Lebesgue number for a simplex whose image lies in the open cover.**  The proof is the proof of
`Work.Cohomology.exists_delta_affineSimplex` with `U ∪ V = univ` replaced by the pullback-cover
identity, which follows from the support condition. -/
theorem exists_delta_of_range_subset {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (σ : Simplex X n)
    (hσ : Set.range (fun z : (Delta n : TopCat) => sdMap n σ z) ⊆ U ∪ V) :
    ∃ δ > 0, ∀ (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))),
      meshVF v < δ → (Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ U ∨
                      Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ V) := by
  set f : Delta n ⟶ X := sdMap n σ with hf
  have hAB : f ⁻¹' U ∪ f ⁻¹' V = (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) := by
    rw [← Set.preimage_union]
    ext z
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact hσ ⟨z, rfl⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_delta_openCover (Z := stdSimplex ℝ (Fin (n + 1)))
    (f ⁻¹' U) (f ⁻¹' V) (hU.preimage f.hom.continuous) (hV.preimage f.hom.continuous) hAB
  refine ⟨δ, hδpos, ?_⟩
  intro k v hv
  have hne : (Set.range (affineSimplex v)).Nonempty :=
    ⟨affineSimplex v (stdSimplex.vertex 0), Set.mem_range_self _⟩
  have hdiam : ∀ x ∈ Set.range (affineSimplex v), ∀ y ∈ Set.range (affineSimplex v),
      dist x y < δ := by
    rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
    exact lt_of_le_of_lt (dist_affineSimplex_le_meshVF v s t) hv
  rcases hδ _ hne hdiam with hU' | hV'
  · left
    rintro y ⟨z, rfl⟩
    exact hU' ⟨z, rfl⟩
  · right
    rintro y ⟨z, rfl⟩
    exact hV' ⟨z, rfl⟩

end

end Work.Cohomology

namespace Work.Whitney

open Work.Cohomology

noncomputable section

/-- **Some iterate of the subdivision sends a simplex supported in the open cover into the small
chains.**  Localised form of `Work.Cohomology.exists_iter_small` (same proof, with
`Work.Cohomology.exists_delta_of_range_subset` in place of
`Work.Cohomology.exists_delta_affineSimplex`). -/
theorem sdIter_small_of_range {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (σ : Simplex X n)
    (hσ : Set.range (fun z : (Delta n : TopCat) => sdMap n σ z) ⊆ U ∪ V) :
    ∃ N, IsSmallChain U V
      ((sdChainMapIter X N).f n (gen X n σ)) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_of_range_subset U V hU hV n σ hσ
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

end Work.Whitney
