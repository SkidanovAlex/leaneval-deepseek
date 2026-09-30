import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- General combinatorial core: if `h` vanishes off `A`, translating the argument does not
increase the sum of squares over `A`. -/
lemma sum_shift_sq_le {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Finset V) (h : V → ℕ) (d : V) (hh : ∀ w, w ∉ A → h w = 0) :
    ∑ v ∈ A, h (v + d) ^ 2 ≤ ∑ v ∈ A, h v ^ 2 := by
  have hinj : Set.InjOn (fun v : V => v + d) (A.filter (fun v => v + d ∈ A)) :=
    fun x _ y _ hxy => add_right_cancel hxy
  have hsub : A.filter (fun v => v + d ∈ A) ⊆ A := Finset.filter_subset _ _
  have hzero : ∀ v ∈ A, v ∉ A.filter (fun v => v + d ∈ A) → h (v + d) ^ 2 = 0 := by
    intro v hv hvnot
    have : v + d ∉ A := by
      intro hmem
      exact hvnot (Finset.mem_filter.mpr ⟨hv, hmem⟩)
    simp [hh (v + d) this]
  calc ∑ v ∈ A, h (v + d) ^ 2
      = ∑ v ∈ A.filter (fun v => v + d ∈ A), h (v + d) ^ 2 := (Finset.sum_subset hsub hzero).symm
    _ = ∑ u ∈ (A.filter (fun v => v + d ∈ A)).image (fun v => v + d), h u ^ 2 :=
          (Finset.sum_image (f := fun u => h u ^ 2)
            (fun x _ y _ hxy => add_right_cancel hxy)).symm
    _ ≤ ∑ u ∈ A, h u ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            rw [Finset.mem_image] at hu
            obtain ⟨v, hv, rfl⟩ := hu
            exact (Finset.mem_filter.mp hv).2
          · intro i _ _
            exact Nat.zero_le _

/-- **Translating the moment map does not increase the fibre `L²` mass.**  For a map `f : S → V`
into an additive commutative group, the sum of squares of the fibre counts at the shifted values
`v + d` (`v` ranging over the values actually attained by `f`) is at most the sum of squares of the
fibre counts. -/
theorem sum_fiber_sq_shift_le {S V : Type*} [Fintype S] [AddCommGroup V] [DecidableEq V]
    (f : S → V) (d : V) :
    (∑ v ∈ (Finset.univ : Finset S).image f,
        ((Finset.univ : Finset S).filter (fun y => f y = v + d)).card ^ 2)
      ≤ ∑ v ∈ (Finset.univ : Finset S).image f,
        ((Finset.univ : Finset S).filter (fun x => f x = v)).card ^ 2 := by
  refine sum_shift_sq_le ((Finset.univ : Finset S).image f)
    (fun w => ((Finset.univ : Finset S).filter (fun x => f x = w)).card) d ?_
  intro w hw
  rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  rw [Finset.mem_filter] at hx
  exact hw (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx.2⟩)

end Work.BMF.recursion
