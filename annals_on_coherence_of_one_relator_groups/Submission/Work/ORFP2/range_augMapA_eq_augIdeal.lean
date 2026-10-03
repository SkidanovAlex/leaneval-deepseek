import Mathlib
import Submission.Work.ORFP2.CosetProj

namespace Work.ORFP2

open MonoidAlgebra

/-- If `S` generates a group `H`, then every `g - 1` (`g : H`) lies in the left `k[H]`-span of
the elements `s - 1` (`s ∈ S`).  The proof follows `g` along the expression of `g` as a product
of elements of `S` and their inverses, using
`(a*b - 1) = a*(b - 1) + (a - 1)` and `(a⁻¹ - 1) = -a⁻¹*(a - 1)`. -/
private lemma single_sub_one_mem_span_of_closure (k : Type*) [CommRing k] (H : Type*) [Group H]
    (S : Finset H) (g : H) (hg : g ∈ Subgroup.closure (S : Set H)) :
    MonoidAlgebra.single g (1 : k) - 1 ∈
      Submodule.span (MonoidAlgebra k H)
        (Set.range fun s : S => MonoidAlgebra.single (s : H) (1 : k) - 1) := by
  classical
  set L : Submodule (MonoidAlgebra k H) (MonoidAlgebra k H) :=
    Submodule.span (MonoidAlgebra k H)
      (Set.range fun s : S => MonoidAlgebra.single (s : H) (1 : k) - 1) with hL
  have hgen : ∀ s : S, MonoidAlgebra.single (s : H) (1 : k) - 1 ∈ L :=
    fun s => Submodule.subset_span ⟨s, rfl⟩
  refine Subgroup.closure_induction (p := fun x _ => MonoidAlgebra.single x (1 : k) - 1 ∈ L)
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    exact hgen ⟨x, hx⟩
  · rw [← MonoidAlgebra.one_def]
    simp
  · intro x y _ _ ihx ihy
    have hmul : MonoidAlgebra.single (x * y) (1 : k) - 1 =
        MonoidAlgebra.single x (1 : k) * (MonoidAlgebra.single y (1 : k) - 1)
          + (MonoidAlgebra.single x (1 : k) - 1) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one]
      noncomm_ring
    rw [hmul]
    exact L.add_mem (Ideal.mul_mem_left L _ ihy) ihx
  · intro x _ ihx
    have hinv : MonoidAlgebra.single x⁻¹ (1 : k) - 1 =
        -(MonoidAlgebra.single x⁻¹ (1 : k) * (MonoidAlgebra.single x (1 : k) - 1)) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one, inv_mul_cancel,
        ← MonoidAlgebra.one_def]
      noncomm_ring
    rw [hinv]
    exact L.neg_mem (Ideal.mul_mem_left L _ ihx)

theorem range_augMapA_eq_augIdeal (k : Type*) [CommRing k] (H : Type*) [Group H] (S : Finset H)
    (hS : Subgroup.closure (S : Set H) = ⊤) : LinearMap.range (augMapA k H S) = augIdeal k H := by
  classical
  have hrange : LinearMap.range (augMapA k H S) =
      Submodule.span (MonoidAlgebra k H)
        (Set.range fun s : S => MonoidAlgebra.single (s : H) (1 : k) - 1) := by
    rw [augMapA, Finsupp.range_linearCombination]
  have haug : augIdeal k H =
      Submodule.span (MonoidAlgebra k H)
        (Set.range fun g : H => MonoidAlgebra.single g (1 : k) - 1) := rfl
  rw [hrange, haug]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro y ⟨s, rfl⟩
    exact ⟨(s : H), rfl⟩
  · apply Submodule.span_le.mpr
    rintro y ⟨g, rfl⟩
    exact single_sub_one_mem_span_of_closure k H S g (hS.symm ▸ Subgroup.mem_top g)

end Work.ORFP2
