import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

theorem perm_eq_one_of_card_three {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α} (hα : Fintype.card α = 3) (hσ : σ ^ 3 = 1) (hfix : ∃ x : α, σ x = x) : σ = 1 := by
  obtain ⟨x, hx⟩ := hfix
  ext y
  rw [Equiv.Perm.one_apply]
  by_contra hy
  -- hy : σ y ≠ y, so y, σ y, σ (σ y) are pairwise distinct and cover α
  have h2 : σ (σ y) ≠ y := by
    intro h
    have h3y : (σ ^ 3) y = y := by rw [hσ, Equiv.Perm.one_apply]
    have hstep : (σ ^ 3) y = σ y := by
      calc (σ ^ 3) y = σ (σ (σ y)) := rfl
        _ = σ y := by rw [h]
    rw [h3y] at hstep
    exact hy hstep.symm
  have h3 : σ (σ y) ≠ σ y := by
    intro h
    exact hy (σ.injective h)
  have hcard : ({y, σ y, σ (σ y)} : Finset α).card = 3 := by
    exact Finset.card_eq_three.mpr ⟨y, σ y, σ (σ y), Ne.symm hy, Ne.symm h2, Ne.symm h3, rfl⟩
  have huniv : ({y, σ y, σ (σ y)} : Finset α) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hα])
  have hxmem : x ∈ ({y, σ y, σ (σ y)} : Finset α) := by
    rw [huniv]; exact Finset.mem_univ x
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with h | h | h
  · rw [h] at hx
    exact hy hx
  · rw [h] at hx
    exact h3 hx
  · rw [h] at hx
    have h3y : (σ ^ 3) y = y := by rw [hσ, Equiv.Perm.one_apply]
    have hx' : y = σ (σ y) := by
      calc y = (σ ^ 3) y := h3y.symm
        _ = σ (σ (σ y)) := rfl
        _ = σ (σ y) := hx
    exact h2 hx'.symm

end Work.Hering.Step4
