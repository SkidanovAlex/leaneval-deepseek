import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

/-- If `α` has cardinality `3` and `τ : Equiv.Perm α` satisfies `τ ^ 3 = 1`, `τ ≠ 1`, then `τ`
is a `3`-cycle: it has no fixed point, and it is transitive on `α`. -/
theorem isCycle_of_card_three {α : Type*} [Fintype α] [DecidableEq α] {τ : Equiv.Perm α}
    (hα : Fintype.card α = 3) (hτ : τ ^ 3 = 1) (hne : τ ≠ 1) : τ.IsCycle := by
  -- `τ` moves some point `a`
  have hane : ∃ a : α, τ a ≠ a := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (Equiv.ext (by intro x; simpa using h x))
  obtain ⟨a, ha⟩ := hane
  -- the three points `a`, `τ a`, `τ² a` are pairwise distinct
  have h2 : (τ ^ 2) a ≠ a := by
    intro h
    apply ha
    calc τ a = τ ((τ ^ 2) a) := by rw [h]
      _ = (τ * τ ^ 2) a := by rw [Equiv.Perm.mul_apply]
      _ = (τ ^ 3) a := by congr 1
      _ = a := by rw [hτ]; rfl
  have h3 : τ a ≠ (τ ^ 2) a := by
    intro h
    rw [pow_two, Equiv.Perm.mul_apply] at h
    exact ha (τ.injective h).symm
  have hcard : ({a, τ a, (τ ^ 2) a} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm ha, Ne.symm h2⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact h3),
        Finset.card_singleton]
  -- hence the orbit of `a` covers all of `α`
  have huniv : ({a, τ a, (τ ^ 2) a} : Finset α) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hα])
  have hcover : ∀ x : α, ∃ i : ℕ, (τ ^ i) a = x := by
    intro x
    have hx : x ∈ ({a, τ a, (τ ^ 2) a} : Finset α) := by
      rw [huniv]; exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  refine ⟨a, ha, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := hcover y
  exact ⟨(i : ℤ), by rw [zpow_natCast]; exact hi⟩

/-- If `α` has cardinality `3` and `τ : Equiv.Perm α` satisfies `τ ^ 3 = 1`, `τ ≠ 1`, then `τ`
acts fixed-point freely on `α`. -/
theorem support_eq_univ_of_card_three {α : Type*} [Fintype α] [DecidableEq α] {τ : Equiv.Perm α}
    (hα : Fintype.card α = 3) (hτ : τ ^ 3 = 1) (hne : τ ≠ 1) : τ.support = Finset.univ := by
  have hane : ∃ a : α, τ a ≠ a := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (Equiv.ext (by intro x; simpa using h x))
  obtain ⟨a, ha⟩ := hane
  have h2 : (τ ^ 2) a ≠ a := by
    intro h
    apply ha
    calc τ a = τ ((τ ^ 2) a) := by rw [h]
      _ = (τ * τ ^ 2) a := by rw [Equiv.Perm.mul_apply]
      _ = (τ ^ 3) a := by congr 1
      _ = a := by rw [hτ]; rfl
  have h3 : τ a ≠ (τ ^ 2) a := by
    intro h
    rw [pow_two, Equiv.Perm.mul_apply] at h
    exact ha (τ.injective h).symm
  have hcard : ({a, τ a, (τ ^ 2) a} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm ha, Ne.symm h2⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact h3),
        Finset.card_singleton]
  have huniv : ({a, τ a, (τ ^ 2) a} : Finset α) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hα])
  have hcover : ∀ x : α, ∃ i : ℕ, (τ ^ i) a = x := by
    intro x
    have hx : x ∈ ({a, τ a, (τ ^ 2) a} : Finset α) := by
      rw [huniv]; exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  ext x
  rw [Equiv.Perm.mem_support]
  simp only [Finset.mem_univ, iff_true]
  intro hx
  obtain ⟨i, hi⟩ := hcover x
  have hy : (τ ^ (i + 1)) a = (τ ^ i) a := by
    rw [pow_succ', Equiv.Perm.mul_apply, hi, hx, ← hi]
  have hfin : (τ ^ i) (τ a) = (τ ^ i) a := by
    simpa only [pow_succ, Equiv.Perm.mul_apply] using hy
  exact ha ((τ ^ i).injective hfin)

/-- On a set of cardinality `3`, a permutation `σ` commuting with an element `τ ≠ 1` of order
dividing `3` is a power of `τ`: `τ` is a `3`-cycle, so `⟨τ⟩` (of order `3`) is exactly the
centralizer of `τ` in `Equiv.Perm α`. -/
theorem mem_zpowers_of_commute_of_card_three {α : Type*} [Fintype α] [DecidableEq α]
    {σ τ : Equiv.Perm α} (hα : Fintype.card α = 3) (hτ : τ ^ 3 = 1) (hne : τ ≠ 1)
    (hc : Commute σ τ) : σ ∈ Subgroup.zpowers τ := by
  have hcyc : τ.IsCycle := isCycle_of_card_three hα hτ hne
  have hsupp : τ.support = Finset.univ := support_eq_univ_of_card_three hα hτ hne
  -- `IsCycle.commute_iff` reduces commutativity with the cycle `τ` to membership in `⟨τ⟩`
  obtain ⟨hc'', hmem⟩ := (Equiv.Perm.IsCycle.commute_iff hcyc).mp hc
  -- as `τ` has full support, the associated permutation is `σ` itself
  have heq : Equiv.Perm.ofSubtype (σ.subtypePerm hc'') = σ := by
    ext x
    exact Equiv.Perm.ofSubtype_subtypePerm_of_mem hc''
      (by rw [hsupp]; exact Finset.mem_univ x)
  rwa [← heq]

end Work.Hering.Step4
