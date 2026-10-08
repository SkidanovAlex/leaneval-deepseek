import Mathlib

namespace Work.AUTA7.A7

/-- If `A` has index two in `G` and `C` is a subgroup of `G` not contained in `A`, then
`C ⊓ A` has index two in `C`, i.e. `|C ⊓ A| * 2 = |C|`.

In relative-index form: `(C ⊓ A).relIndex C = 2`, since an element `a ∈ C \ A` and the
index-two property of `A` show that every element of `C` lies in exactly one of `C ⊓ A` and
`(C ⊓ A) * a`; `Subgroup.relIndex_mul_card` then converts this into the cardinality identity. -/
theorem CardInfMulTwoOfIndexTwo {G : Type*} [Group G] (A C : Subgroup G) (hA : A.index = 2)
    (hC : ¬ C ≤ A) : Nat.card ↥(C ⊓ A) * 2 = Nat.card ↥C := by
  -- Pick an element of `C` outside `A`; it witnesses that `C ⊓ A` is a proper subgroup of `C`.
  obtain ⟨a, haC, haA⟩ : ∃ a ∈ C, a ∉ A := by
    by_contra h
    refine hC fun x hx => ?_
    by_contra hxA
    exact h ⟨x, hx, hxA⟩
  -- Since `A` has index two, multiplying an element outside `A` by `a` brings it back into `A`.
  have hmul : ∀ b : G, b ∉ A → b * a ∈ A := by
    intro b hb
    rw [Subgroup.mul_mem_iff_of_index_two hA]
    simp [hb, haA]
  -- Hence `C ⊓ A` has relative index two in `C`.
  have hrel : (C ⊓ A).relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨a, haC, fun h => haA h.2, ?_⟩
    intro b hbC
    by_cases hbA : b ∈ A
    · exact Or.inr (Subgroup.mem_inf.mpr ⟨hbC, hbA⟩)
    · exact Or.inl (Subgroup.mem_inf.mpr ⟨mul_mem hbC haC, hmul b hbA⟩)
  -- Lagrange's theorem for the pair `C ⊓ A ≤ C` gives `|C ⊓ A| * 2 = |C|`.
  have hcard := Subgroup.relIndex_mul_card (C ⊓ A) C
  rw [hrel, inf_eq_left.mpr inf_le_left] at hcard
  rw [mul_comm] at hcard
  exact hcard

end Work.AUTA7.A7
