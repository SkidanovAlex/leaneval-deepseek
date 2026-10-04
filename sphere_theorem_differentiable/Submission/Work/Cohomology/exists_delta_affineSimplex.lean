import Mathlib
import Submission.Work.Cohomology.Mesh
import Submission.Work.Cohomology.SmallChains

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A Lebesgue number for affine simplices: small affine simplices are `U`- or `V`-small

Let `U, V ⊆ X` be an open cover of a topological space and `σ : Δⁿ ⟶ X` a singular simplex.  The
aim of this file is the geometric input to the small-simplices theorem: there is a positive `δ`
such that **every** affine simplex of **any** dimension whose vertex family has mesh `< δ` is,
after being pushed forward by `σ`, entirely contained in `U` or entirely in `V`.

The proof is the classical Lebesgue-number argument.

* On `Δⁿ` (a compact metric space) the sets `σ⁻¹U`, `σ⁻¹V` form an open cover, so there is `δ > 0`
  such that any two points at distance `< δ` lie in a common member of the cover
  (`lebesgue_delta_openCover`; this is `Metric.lebesgue_number_lemma_of_metric` recast in the form
  needed here).
* The image of an affine simplex `affineSimplex v` is the convex hull of the vertex family `v`
  (`dist_affineSimplex_le_meshVF`), so its diameter is at most `meshVF v` — the diameter of the
  convex hull of a set equals the diameter of the set (`convexHull_diam`).

## Main result

* `exists_delta_affineSimplex` — the statement requested by the small-simplices chapter.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Lebesgue number for a two-element open cover.**  If `A, B` are open and cover a compact
metric space `Z`, then there is `δ > 0` such that every *pairwise `δ`-close* nonempty subset of `Z`
is contained in `A` or in `B`. -/
theorem lebesgue_delta_openCover {Z : Type*} [PseudoMetricSpace Z] [CompactSpace Z]
    (A B : Set Z) (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = Set.univ) :
    ∃ δ > 0, ∀ S : Set Z, S.Nonempty →
      (∀ x ∈ S, ∀ y ∈ S, dist x y < δ) → S ⊆ A ∨ S ⊆ B := by
  set c : Bool → Set Z := fun i => if i then A else B with hc
  have hopen : ∀ i, IsOpen (c i) := by
    intro i
    by_cases h : i = true
    · rw [h]; exact hA
    · rw [Bool.not_eq_true] at h; rw [h]; exact hB
  have hcover : (Set.univ : Set Z) ⊆ ⋃ i, c i := by
    intro x _
    have hx' : x ∈ A ∪ B := by rw [hAB]; trivial
    rcases hx' with hx' | hx'
    · exact Set.mem_iUnion.mpr ⟨true, by simp [c, hx']⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simp [c, hx']⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := Set.univ) (c := c)
    isCompact_univ hopen hcover
  refine ⟨δ, hδpos, ?_⟩
  intro S hS hdist
  obtain ⟨x, hxS⟩ := hS
  obtain ⟨i, hi⟩ := hδ x trivial
  have hsub : S ⊆ c i := by
    intro y hy
    exact hi (by rw [Metric.mem_ball, dist_comm]; exact hdist x hxS y hy)
  cases i
  · exact Or.inr (by simpa [c] using hsub)
  · exact Or.inl (by simpa [c] using hsub)

/-- **The image of an affine simplex has diameter at most the mesh of its vertex family.**  The
range of `affineSimplex v` is the convex hull of the vertices `v`, and the diameter of a convex hull
equals the diameter of the generating set. -/
theorem dist_affineSimplex_le_meshVF {N k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)))
    (s t : stdSimplex ℝ (Fin (k + 1))) :
    dist (affineSimplex v s) (affineSimplex v t) ≤ meshVF v := by
  have hcoe : ∀ r : stdSimplex ℝ (Fin (k + 1)),
      (affineSimplex v r : Fin (N + 1) → ℝ) = ∑ j, r j • (v j : Fin (N + 1) → ℝ) := by
    intro r; ext i; simp [affineSimplex_apply, Finset.sum_apply, smul_eq_mul]
  set K : Set (Fin (N + 1) → ℝ) := Set.range (fun j => (v j : Fin (N + 1) → ℝ)) with hKdef
  have hmem : ∀ r : stdSimplex ℝ (Fin (k + 1)),
      (∑ j, r j • (v j : Fin (N + 1) → ℝ)) ∈ convexHull ℝ K := by
    intro r
    have hsum : ∑ j, r j = 1 := r.2.2
    have hpos : (0 : ℝ) < ∑ j, r j := by rw [hsum]; norm_num
    have h := Finset.centerMass_mem_convexHull (R := ℝ) (E := Fin (N + 1) → ℝ) (s := K)
      Finset.univ (w := fun j => r j) (fun j _ => r.2.1 j) hpos (fun j _ => Set.mem_range_self j)
    have hcm : Finset.univ.centerMass (fun j => r j) (fun j => (v j : Fin (N + 1) → ℝ))
        = ∑ j, r j • (v j : Fin (N + 1) → ℝ) := by
      rw [Finset.centerMass_eq_of_sum_1]; exact hsum
    rwa [hcm] at h
  have hK : Metric.diam K = meshVF v := by
    rw [meshVF]
    refine le_antisymm ?_ ?_
    · refine Metric.diam_le_of_forall_dist_le Metric.diam_nonneg ?_
      rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
      have h2 : dist (v i) (v j) ≤ Metric.diam (Set.range v) :=
        Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
          (Set.mem_range_self i) (Set.mem_range_self j)
      exact (Subtype.dist_eq (v i) (v j)).symm.le.trans h2
    · refine Metric.diam_le_of_forall_dist_le Metric.diam_nonneg ?_
      rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
      have h2 : dist ((v i : stdSimplex ℝ (Fin (N + 1))) : Fin (N + 1) → ℝ)
          ((v j : stdSimplex ℝ (Fin (N + 1))) : Fin (N + 1) → ℝ) ≤ Metric.diam K :=
        Metric.dist_le_diam_of_mem (Set.finite_range _).isBounded
          (Set.mem_range_self i) (Set.mem_range_self j)
      exact (Subtype.dist_eq (v i) (v j)).le.trans h2
  calc dist (affineSimplex v s) (affineSimplex v t)
      = dist (affineSimplex v s : Fin (N + 1) → ℝ) (affineSimplex v t) := Subtype.dist_eq _ _
    _ ≤ Metric.diam (convexHull ℝ K) :=
        Metric.dist_le_diam_of_mem
          (isBounded_convexHull.mpr (Set.finite_range _).isBounded)
          (by rw [hcoe]; exact hmem s) (by rw [hcoe]; exact hmem t)
    _ = Metric.diam K := convexHull_diam _
    _ = meshVF v := hK

theorem exists_delta_affineSimplex {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) (σ : Simplex X n) :
    ∃ δ > 0, ∀ (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))),
      meshVF v < δ → (Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ U ∨
                      Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ V) := by
  set f : Delta n ⟶ X := sdMap n σ with hf
  have hAB : f ⁻¹' U ∪ f ⁻¹' V = (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) := by
    rw [← Set.preimage_union, hUV, Set.preimage_univ]
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
