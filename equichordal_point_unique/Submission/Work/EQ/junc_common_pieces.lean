import Mathlib

open Set

namespace Work.EQ

/-- Pigeonhole principle for maps into a countable type: an uncountable domain has an
uncountable fibre. -/
lemma exists_uncountable_fiber {α β : Type*} [Countable β]
    (f : α → β) (hα : ¬ Countable α) :
    ∃ b : β, ¬ (f ⁻¹' {b}).Countable := by
  by_contra h
  push Not at h
  exact hα (Countable.of_preimage_singleton h)

/-- Pigeonhole over a countable family of pieces. If an uncountable set `Z` of parameter values can each be matched, at every level `j : Fin N`, to some piece `p ∈ Sp j` with `w ∈ p.1` and `L (j.val + 1) w = p.2 w`, then there is a single tuple `t` of pieces and an uncountable `Z' ⊆ Z` on which that tuple works simultaneously for every level. -/
theorem junc_common_pieces {N : ℕ}
    {Sp : Fin N → Set (Set ℂ × (ℂ → ℂ × ℂ))} (hSpc : ∀ j, (Sp j).Countable)
    {L : ℕ → ℂ → ℂ × ℂ} {Z : Set ℂ} (hZ : ¬ Z.Countable)
    (hcov : ∀ w ∈ Z, ∀ j : Fin N, ∃ p ∈ Sp j, w ∈ p.1 ∧ L (j.val + 1) w = p.2 w) :
    ∃ (t : (j : Fin N) → (Set ℂ × (ℂ → ℂ × ℂ))) (Z' : Set ℂ),
      (∀ j, t j ∈ Sp j) ∧ Z' ⊆ Z ∧ ¬ Z'.Countable ∧
      (∀ w ∈ Z', ∀ j : Fin N, w ∈ (t j).1 ∧ L (j.val + 1) w = (t j).2 w) := by
  classical
  -- For each `z : ↥Z` and each level `j`, choose a valid piece.
  let g : ↥Z → ((j : Fin N) → ↥(Sp j)) :=
    fun z j => ⟨Classical.choose (hcov z.1 z.2 j),
      (Classical.choose_spec (hcov z.1 z.2 j)).1⟩
  -- Each `Sp j` is countable, so the (finite) product of choices is countable.
  haveI : ∀ j, Countable ↥(Sp j) := fun j => (hSpc j).to_subtype
  haveI : Countable ((j : Fin N) → ↥(Sp j)) := inferInstance
  have hZc : ¬ Countable ↥Z := fun h => hZ (Set.countable_coe_iff.mp h)
  -- Pigeonhole: some chosen tuple is used on an uncountable set of parameters.
  obtain ⟨t₀, ht₀⟩ := exists_uncountable_fiber g hZc
  refine ⟨fun j => (t₀ j).1, Subtype.val '' (g ⁻¹' {t₀}), ?_, ?_, ?_, ?_⟩
  · intro j; exact (t₀ j).2
  · rintro w ⟨z, hz, rfl⟩; exact z.2
  · intro hc
    have hinj : InjOn (Subtype.val : ↥Z → ℂ) (g ⁻¹' {t₀}) := fun a _ b _ h => Subtype.ext h
    exact ht₀ (countable_of_injective_of_countable_image hinj hc)
  · rintro w ⟨z, hz, rfl⟩ j
    have hg_eq : g z = t₀ := hz
    have hspec := Classical.choose_spec (hcov z.1 z.2 j)
    obtain ⟨hpmem, hwmem, hwL⟩ := hspec
    have hzg : g z j = t₀ j := by rw [hg_eq]
    constructor
    · show z.1 ∈ ((t₀ j).1).1
      rw [← hzg]; exact hwmem
    · show L (j.val + 1) z.1 = ((t₀ j).1).2 z.1
      rw [← hzg]; exact hwL

end Work.EQ
