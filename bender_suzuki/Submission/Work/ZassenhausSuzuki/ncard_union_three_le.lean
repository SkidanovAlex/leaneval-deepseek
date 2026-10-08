import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem ncard_union_three_le {α : Type*} [Finite α] (S₁ S₂ S₃ : Set α) (a : α)
    (h12 : S₁ ∩ S₂ = {a}) (h13 : S₁ ∩ S₃ = {a}) (h23 : S₂ ∩ S₃ = {a}) :
    S₁.ncard + S₂.ncard + S₃.ncard - 2 ≤ (S₁ ∪ S₂ ∪ S₃).ncard := by
  -- Inclusion–exclusion on `S₁ ∪ S₂`.
  have hA : (S₁ ∪ S₂).ncard + 1 = S₁.ncard + S₂.ncard := by
    have h := Set.ncard_union_add_ncard_inter S₁ S₂
    rw [h12, Set.ncard_singleton] at h
    exact h
  -- Inclusion–exclusion on `(S₁ ∪ S₂) ∪ S₃`, using `(S₁ ∪ S₂) ∩ S₃ = {a}`.
  have hB : (S₁ ∪ S₂ ∪ S₃).ncard + 1 = (S₁ ∪ S₂).ncard + S₃.ncard := by
    have h := Set.ncard_union_add_ncard_inter (S₁ ∪ S₂) S₃
    have hI : (S₁ ∪ S₂) ∩ S₃ = {a} := by
      rw [Set.union_inter_distrib_right, h13, h23, Set.union_self]
    rw [hI, Set.ncard_singleton] at h
    exact h
  have hsum : (S₁ ∪ S₂ ∪ S₃).ncard + 2 = S₁.ncard + S₂.ncard + S₃.ncard := by
    omega
  omega

end Work.ZassenhausSuzuki
