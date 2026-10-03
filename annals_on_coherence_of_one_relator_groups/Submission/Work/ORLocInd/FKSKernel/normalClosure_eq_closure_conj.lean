import Mathlib

namespace Work.ORLocInd.FKSKernel

universe u

/-- For a subgroup `A` of a group, the subgroup of elements `k` such that both `k` and
`k⁻¹` normalize `A` elementwise (via `k * (-) * k⁻¹` and `k⁻¹ * (-) * k`). -/
def normSub {X : Type u} (A : Subgroup (FreeGroup X)) : Subgroup (FreeGroup X) where
  carrier := {k | ∀ n ∈ A, k * n * k⁻¹ ∈ A ∧ k⁻¹ * n * k ∈ A}
  mul_mem' := by
    intro k1 k2 h1 h2 n hn
    refine ⟨?_, ?_⟩
    · have h2n : k2 * n * k2⁻¹ ∈ A := (h2 n hn).1
      have h := (h1 (k2 * n * k2⁻¹) h2n).1
      rwa [show (k1 * k2) * n * (k1 * k2)⁻¹ = k1 * (k2 * n * k2⁻¹) * k1⁻¹ by group]
    · have h1n : k1⁻¹ * n * k1 ∈ A := (h1 n hn).2
      have h := (h2 (k1⁻¹ * n * k1) h1n).2
      rwa [show (k1 * k2)⁻¹ * n * (k1 * k2) = k2⁻¹ * (k1⁻¹ * n * k1) * k2 by group]
  one_mem' := by
    intro n hn
    constructor <;> simpa using hn
  inv_mem' := by
    intro k hk n hn
    have := hk n hn
    simpa using ⟨this.2, this.1⟩

@[simp] theorem mem_normSub {X : Type u} {A : Subgroup (FreeGroup X)} {k : FreeGroup X} :
    k ∈ normSub A ↔ ∀ n ∈ A, k * n * k⁻¹ ∈ A ∧ k⁻¹ * n * k ∈ A := Iff.rfl

/-- For a subgroup `A` and an element `g`, the subgroup of elements `n` whose two conjugates
by `g` lie in `A`. -/
def conjSub {X : Type u} (A : Subgroup (FreeGroup X)) (g : FreeGroup X) : Subgroup (FreeGroup X) where
  carrier := {n | g * n * g⁻¹ ∈ A ∧ g⁻¹ * n * g ∈ A}
  mul_mem' := by
    intro n1 n2 h1 h2
    refine ⟨?_, ?_⟩
    · rw [show g * (n1 * n2) * g⁻¹ = (g * n1 * g⁻¹) * (g * n2 * g⁻¹) by group]
      exact A.mul_mem h1.1 h2.1
    · rw [show g⁻¹ * (n1 * n2) * g = (g⁻¹ * n1 * g) * (g⁻¹ * n2 * g) by group]
      exact A.mul_mem h1.2 h2.2
  one_mem' := by
    constructor <;> simp
  inv_mem' := by
    intro n hn
    refine ⟨?_, ?_⟩
    · rw [show g * n⁻¹ * g⁻¹ = (g * n * g⁻¹)⁻¹ by group]
      exact A.inv_mem hn.1
    · rw [show g⁻¹ * n⁻¹ * g = (g⁻¹ * n * g)⁻¹ by group]
      exact A.inv_mem hn.2

@[simp] theorem mem_conjSub {X : Type u} {A : Subgroup (FreeGroup X)} {g n : FreeGroup X} :
    n ∈ conjSub A g ↔ g * n * g⁻¹ ∈ A ∧ g⁻¹ * n * g ∈ A := Iff.rfl

theorem mem_normSub_iff_le_conjSub {X : Type u} {A : Subgroup (FreeGroup X)} {k : FreeGroup X} :
    k ∈ normSub A ↔ A ≤ conjSub A k := by
  rw [mem_normSub]
  constructor
  · intro h n hn; exact h n hn
  · intro h n hn; exact h hn

theorem normalClosure_eq_closure_conj {X : Type u} (a : X) :
    Subgroup.normalClosure ({FreeGroup.of a} : Set (FreeGroup X)) =
      Subgroup.closure {g : FreeGroup X |
        ∃ k ∈ Subgroup.closure (FreeGroup.of '' {b : X | b ≠ a}),
          g = k * FreeGroup.of a * k⁻¹} := by
  classical
  set H : Subgroup (FreeGroup X) :=
    Subgroup.closure (FreeGroup.of '' {b : X | b ≠ a}) with hH
  set C : Set (FreeGroup X) :=
    {g : FreeGroup X | ∃ k ∈ H, g = k * FreeGroup.of a * k⁻¹} with hC
  set A : Subgroup (FreeGroup X) := Subgroup.closure C with hA
  have hofA : FreeGroup.of a ∈ A := by
    rw [hA]
    exact Subgroup.subset_closure ⟨1, Subgroup.one_mem H, by simp⟩
  -- Every generator of `H` normalizes `A`.
  have hgenH : ∀ b : X, b ≠ a → FreeGroup.of b ∈ normSub A := by
    intro b hb
    rw [mem_normSub_iff_le_conjSub]
    have hbH : FreeGroup.of b ∈ H := Subgroup.subset_closure ⟨b, hb, rfl⟩
    apply (Subgroup.closure_le _).mpr
    intro n hn
    obtain ⟨k, hk, rfl⟩ := hn
    refine ⟨?_, ?_⟩
    · have hbk : FreeGroup.of b * k ∈ H := H.mul_mem hbH hk
      have hmem : (FreeGroup.of b * k) * FreeGroup.of a * (FreeGroup.of b * k)⁻¹ ∈ A := by
        rw [hA]
        exact Subgroup.subset_closure ⟨FreeGroup.of b * k, hbk, rfl⟩
      rwa [show FreeGroup.of b * (k * FreeGroup.of a * k⁻¹) * (FreeGroup.of b)⁻¹
        = (FreeGroup.of b * k) * FreeGroup.of a * (FreeGroup.of b * k)⁻¹ by group]
    · have hbk : (FreeGroup.of b)⁻¹ * k ∈ H := H.mul_mem (H.inv_mem hbH) hk
      have hmem : ((FreeGroup.of b)⁻¹ * k) * FreeGroup.of a * ((FreeGroup.of b)⁻¹ * k)⁻¹ ∈ A := by
        rw [hA]
        exact Subgroup.subset_closure ⟨(FreeGroup.of b)⁻¹ * k, hbk, rfl⟩
      rwa [show (FreeGroup.of b)⁻¹ * (k * FreeGroup.of a * k⁻¹) * FreeGroup.of b
        = ((FreeGroup.of b)⁻¹ * k) * FreeGroup.of a * ((FreeGroup.of b)⁻¹ * k)⁻¹ by group]
  have hgen_a : FreeGroup.of a ∈ normSub A := by
    rw [mem_normSub]
    intro n hn
    exact ⟨A.mul_mem (A.mul_mem hofA hn) (A.inv_mem hofA),
      A.mul_mem (A.mul_mem (A.inv_mem hofA) hn) hofA⟩
  have hH_le : H ≤ normSub A := by
    rw [hH]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hgenH b hb
  -- The whole free group normalizes `A`.
  have htop : (⊤ : Subgroup (FreeGroup X)) ≤ normSub A := by
    rw [← FreeGroup.closure_range_of X]
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    by_cases hx : x = a
    · subst hx; exact hgen_a
    · exact hH_le (Subgroup.subset_closure ⟨x, hx, rfl⟩)
  have hAnormal : A.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h : ∀ m ∈ A, g * m * g⁻¹ ∈ A ∧ g⁻¹ * m * g ∈ A := by
      have hg := htop (Subgroup.mem_top g)
      rwa [mem_normSub] at hg
    exact (h n hn).1
  have h1 : Subgroup.normalClosure ({FreeGroup.of a} : Set (FreeGroup X)) ≤ A := by
    have hAn : A.Normal := hAnormal
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hofA
  have h2 : A ≤ Subgroup.normalClosure ({FreeGroup.of a} : Set (FreeGroup X)) := by
    rw [hA]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact Subgroup.Normal.conj_mem Subgroup.normalClosure_normal (FreeGroup.of a)
      (Subgroup.subset_normalClosure (Set.mem_singleton (FreeGroup.of a))) k
  exact le_antisymm h1 h2

end Work.ORLocInd.FKSKernel
