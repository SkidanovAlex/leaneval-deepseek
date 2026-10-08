import Mathlib

namespace Work.BG

theorem finsupp_sum_univ_eq_sum_support {α β R : Type*} [Fintype β] [Semiring R]
    (f : β → α) (hf : Function.Injective f) (m : α →₀ ℕ)
    (hsupp : ↑m.support ⊆ Set.range f) (g : α → R) :
    ∑ b : β, (m (f b) : R) * g (f b) = ∑ a ∈ m.support, (m a : R) * g a := by
  classical
  -- Drop all `b` with `f b ∉ m.support`: there the summand is zero.
  have hside : ∀ x ∈ (Finset.univ : Finset β),
      x ∉ (Finset.univ.filter (fun b => f b ∈ m.support)) →
      (m (f x) : R) * g (f x) = 0 := by
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hx0 : m (f x) = 0 := by simpa [Finsupp.mem_support_iff] using hx
    rw [hx0]
    simp
  have h1 : (∑ b : β, (m (f b) : R) * g (f b))
      = ∑ b ∈ (Finset.univ.filter (fun b => f b ∈ m.support)), (m (f b) : R) * g (f b) :=
    (Finset.sum_subset (Finset.filter_subset _ _) hside).symm
  rw [h1]
  -- On the filtered index set, `f` is a bijection onto `m.support`.
  exact Finset.sum_bij (fun b _ => f b)
    (fun b hb => by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb)
    (fun b₁ _ b₂ _ h => hf h)
    (fun a ha => by
      obtain ⟨b, hb⟩ := hsupp ha
      exact ⟨b, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hb]
        exact ha, hb⟩)
    (fun b _ => rfl)

end Work.BG
