import Mathlib
import Submission.Work.ORFP2.Basic

set_option autoImplicit false

namespace Work.ORFP2

open MonoidAlgebra

section Crux

variable (k : Type*) [CommRing k] (G : Type*) [Group G]

/-- If `J` is an ideal of `k[G]` then the set of `g : G` with `single g 1 - 1 ∈ J` is a
subgroup of `G`.  (This packages the identities
`(a*b - 1) = a*(b - 1) + (a - 1)` and `(a⁻¹ - 1) = -a⁻¹ * (a - 1)`.) -/
private lemma single_sub_one_subgroup (J : Ideal (MonoidAlgebra k G)) :
    ∃ S : Subgroup G, ∀ g : G, g ∈ S ↔ MonoidAlgebra.single g (1 : k) - 1 ∈ J := by
  refine ⟨{ carrier := {g | MonoidAlgebra.single g (1 : k) - 1 ∈ J},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · intro a b ha hb
    show MonoidAlgebra.single (a * b) (1 : k) - 1 ∈ J
    have h : MonoidAlgebra.single (a * b) (1 : k) - 1 =
        MonoidAlgebra.single a (1 : k) * (MonoidAlgebra.single b (1 : k) - 1)
          + (MonoidAlgebra.single a (1 : k) - 1) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one]
      noncomm_ring
    rw [h]
    exact J.add_mem (J.mul_mem_left _ hb) ha
  · show MonoidAlgebra.single 1 (1 : k) - 1 ∈ J
    rw [← MonoidAlgebra.one_def]
    simp
  · intro a ha
    show MonoidAlgebra.single a⁻¹ (1 : k) - 1 ∈ J
    have h : MonoidAlgebra.single a⁻¹ (1 : k) - 1 =
        -(MonoidAlgebra.single a⁻¹ (1 : k) * (MonoidAlgebra.single a (1 : k) - 1)) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one, ← MonoidAlgebra.one_def]
      noncomm_ring
    rw [h]
    exact J.neg_mem (J.mul_mem_left _ ha)

/-- If `φ : F(α) ↠ G` is surjective then the elements `φ xᵢ - 1` generate the augmentation
ideal of `k[G]`. -/
theorem augIdeal_eq_span_of_surjective (k : Type*) [CommRing k] (G : Type*) [Group G]
    (α : Type*) (φ : FreeGroup α →* G) (hφ : Function.Surjective φ) :
    augIdeal k G =
      Ideal.span (Set.range fun i : α => MonoidAlgebra.single (φ (FreeGroup.of i)) (1 : k) - 1) := by
  set J : Ideal (MonoidAlgebra k G) :=
    Ideal.span (Set.range fun i : α => MonoidAlgebra.single (φ (FreeGroup.of i)) (1 : k) - 1) with hJ
  obtain ⟨S, hS⟩ := single_sub_one_subgroup k G J
  have hgen : ∀ i : α, φ (FreeGroup.of i) ∈ S := fun i => (hS _).mpr (Ideal.subset_span ⟨i, rfl⟩)
  have h2 : Subgroup.closure (Set.range fun i : α => φ (FreeGroup.of i)) = ⊤ := by
    rw [Set.range_comp' (⇑φ) (FreeGroup.of (α := α)), ← MonoidHom.map_closure φ,
      FreeGroup.closure_range_of, Subgroup.map_top_of_surjective φ hφ]
  have htop : S = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← h2]
    exact (Subgroup.closure_le S).mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
  rw [hJ]
  refine le_antisymm ?_ ?_
  · rw [augIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := hφ g
    have : φ x ∈ S := by rw [htop]; exact trivial
    exact (hS (φ x)).mp this
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact single_sub_one_mem_augIdeal k G (φ (FreeGroup.of i))

end Crux

end Work.ORFP2
