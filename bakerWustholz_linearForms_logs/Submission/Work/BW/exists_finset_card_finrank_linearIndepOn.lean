import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-- If a finite family `v : ι → M` spans a subspace of dimension `n`, then some `n` of its
elements are linearly independent: there is a `Finset` of `n` indices on which `v` is linearly
independent. -/
theorem exists_finset_card_finrank_linearIndepOn {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] {ι : Type*} [Fintype ι] {v : ι → M} {n : ℕ}
    (h : Module.finrank K (Submodule.span K (Set.range v)) = n) :
    ∃ s : Finset ι, s.card = n ∧ LinearIndepOn K v (↑s) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- The index type is empty: the spanning set is empty, so `n = 0`.
    haveI := hι
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.card_empty]
      have h0 : Module.finrank K (Submodule.span K (Set.range v)) = 0 := by
        rw [Set.range_eq_empty v, Submodule.span_empty, finrank_bot]
      rw [← h, h0]
    · rw [Finset.coe_empty]
      exact linearIndepOn_empty K v
  · haveI := hι
    -- The span of `v` is finite-dimensional, so it has a linearly independent spanning
    -- subset `t` of `range v` of cardinality `n`.
    haveI : Module.Finite K (Submodule.span K (Set.range v)) :=
      Module.Finite.span_of_finite K (Set.finite_range v)
    obtain ⟨t, ht_sub, ht_card, _ht_span, ht_indep⟩ :=
      Submodule.exists_finset_span_eq_linearIndepOn K (Set.range v)
    -- Choose a preimage under `v` for every element of `t`.
    let c : M → ι := fun x => if hx : x ∈ Set.range v then hx.choose else Classical.arbitrary ι
    have hc : ∀ x ∈ (t : Set M), v (c x) = x := by
      intro x hx
      have hxr : x ∈ Set.range v := ht_sub hx
      simp only [c, dite_eq_left hxr]
      exact hxr.choose_spec
    have hinj : Set.InjOn c (t : Set M) := by
      intro x hx y hy hxy
      rw [← hc x hx, ← hc y hy, hxy]
    refine ⟨t.image c, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, ht_card, h]
    · -- `v` is injective on the chosen index set and its image is exactly `t`.
      have hveq : v '' ((t.image c : Finset ι) : Set ι) = (t : Set M) := by
        ext x
        constructor
        · rintro ⟨i, hi, rfl⟩
          rw [Finset.mem_coe, Finset.mem_image] at hi
          obtain ⟨y, hy, rfl⟩ := hi
          rw [hc y hy]
          exact hy
        · intro hx
          refine ⟨c x, ?_, hc x hx⟩
          rw [Finset.mem_coe, Finset.mem_image]
          exact ⟨x, hx, rfl⟩
      have hinjV : Set.InjOn v ((t.image c : Finset ι) : Set ι) := by
        intro i hi j hj hij
        rw [Finset.mem_coe, Finset.mem_image] at hi hj
        obtain ⟨x, hx, rfl⟩ := hi
        obtain ⟨y, hy, rfl⟩ := hj
        rw [hc x hx, hc y hy] at hij
        rw [hij]
      rw [linearIndepOn_iff_image (f := v) hinjV, hveq]
      exact ht_indep

end Work.BW
