import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion

/-!
# Elementary support bookkeeping for the proof of Hatcher 3.27

This file collects the elementary facts about the submodule `Work.Compact.Noncompact.suppS` of
chains supported in a subset which are used by the final argument
(`Work.Compact.Noncompact.eq_zero_of_forall_localMap_eq_zero`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Compact.Noncompact

noncomputable section

variable {X : TopCat}

/-- A generator whose simplex has image in `S` is supported in `S`. -/
theorem genC_mem_suppS {S : Set X} {k : ℕ} {σ : SimplexT X k} (h : SimplexSet σ ⊆ S) :
    genC X k σ ∈ suppS X S k := by
  obtain ⟨a, ha⟩ := Work.Cohomology.exists_map_inclUX_of_range_subset S
    (Opposite.op (SimplexCategory.mk k)) σ h
  refine ⟨genC (TopCat.of S) k a, ?_⟩
  have h2 := Work.Cohomology.chainComplexMap_ι_apply
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)) k a (1 : ℤ)
  have h3 : (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)).app
      (Opposite.op (SimplexCategory.mk k)) a = σ := ha
  rw [h3] at h2
  exact h2

/-- A multiple of a generator whose simplex has image in `S` is supported in `S`. -/
theorem smul_genC_mem_suppS {S : Set X} {k : ℕ} {σ : SimplexT X k} (h : SimplexSet σ ⊆ S)
    (a : ℤ) : a • genC X k σ ∈ suppS X S k := by
  obtain ⟨τ, hτ⟩ := Work.Cohomology.exists_map_inclUX_of_range_subset S
    (Opposite.op (SimplexCategory.mk k)) σ h
  refine ⟨a • genC (TopCat.of S) k τ, ?_⟩
  show ((Work.Cohomology.inclChains X S).f k).hom (a • genC (TopCat.of S) k τ) = a • genC X k σ
  rw [map_zsmul]
  congr 1
  have h2 := Work.Cohomology.chainComplexMap_ι_apply
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)) k τ (1 : ℤ)
  have h3 : (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)).app
      (Opposite.op (SimplexCategory.mk k)) τ = σ := hτ
  rw [h3] at h2
  exact h2

/-- The image of each singular simplex is preconnected. -/
theorem isPreconnected_simplexSet {k : ℕ} (σ : SimplexT X k) :
    IsPreconnected (SimplexSet σ) := by
  have hcont : Continuous (Work.Homology.toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk k)) σ) :=
    (Work.Homology.toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk k)) σ).continuous
  exact isPreconnected_range hcont

/-- A singular simplex whose image lies in the union of two disjoint open sets has its image in
one of them. -/
theorem simplexSet_subset_or {S T : Set X} (hS : IsOpen S) (hT : IsOpen T) (hd : Disjoint S T)
    {k : ℕ} {σ : SimplexT X k} (h : SimplexSet σ ⊆ S ∪ T) :
    SimplexSet σ ⊆ S ∨ SimplexSet σ ⊆ T :=
  (isPreconnected_simplexSet σ).subset_or_subset hS hT hd h

/-- The sup of the submodules of chains supported in two sets lies in the submodule of chains
supported in their union. -/
theorem suppS_sup_le_union (S T : Set X) (k : ℕ) :
    suppS X S k ⊔ suppS X T k ≤ suppS X (S ∪ T) k :=
  sup_le (suppS_mono Set.subset_union_left k) (suppS_mono Set.subset_union_right k)

/-- **Chains supported in a disjoint union of two open sets split as a sum.** -/
theorem suppS_union_le_sup {S T : Set X} (hS : IsOpen S) (hT : IsOpen T) (hd : Disjoint S T)
    (k : ℕ) : suppS X (S ∪ T) k ≤ suppS X S k ⊔ suppS X T k := by
  classical
  intro c hc
  obtain ⟨T', a, hca, hcond⟩ := (mem_suppS_iff_of_expansion k c (S ∪ T)).mp hc
  rw [hca]
  rw [← Finset.sum_filter_add_sum_filter_not T' (fun σ => SimplexSet σ ⊆ S)]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.sum_mem _ fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    exact Submodule.mem_sup_left (smul_genC_mem_suppS hσ.2 (a σ))
  · refine Submodule.sum_mem _ fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rcases eq_or_ne (a σ) 0 with h0 | h0
    · rw [h0]; simp
    · have hσT : SimplexSet σ ⊆ T := by
        rcases simplexSet_subset_or hS hT hd (hcond σ hσ.1 h0) with h' | h'
        · exact absurd h' hσ.2
        · exact h'
      exact Submodule.mem_sup_right (smul_genC_mem_suppS hσT (a σ))

/-- The image of a singular simplex is nonempty. -/
theorem simplexSet_nonempty {k : ℕ} (σ : SimplexT X k) : (SimplexSet σ).Nonempty := by
  have hmem : (fun _ : Fin (k + 1) => ((k : ℝ) + 1)⁻¹) ∈ stdSimplex ℝ (Fin (k + 1)) := by
    refine ⟨fun i => by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    field_simp
  exact ⟨Work.Homology.toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk k)) σ ⟨_, hmem⟩, ⟨_, rfl⟩⟩

end

end Work.Compact.Noncompact
