import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_doubleCoset_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.DoubleCoset
set_option linter.style.haveILetI false

open scoped Pointwise

theorem card_mul_singleton_mul_mul_card_inf {G : Type*} [Group G] [Finite G] (B : Subgroup G) (g : G) :
    Nat.card ((B : Set G) * ({g} : Set G) * (B : Set G)) * Nat.card ↥(B ⊓ B.map (MulAut.conj g).toMonoidHom) = Nat.card B ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  have hset : (B : Set G) * ({g} : Set G) * (B : Set G) =
      {y : G | ∃ a b : B, y = (a : G) * g * (b : G)} := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_mul] at hy
      rcases hy with ⟨x, hx, z, hz, hxz⟩
      rw [Set.mem_mul] at hx
      rcases hx with ⟨a, ha, w, hw, haw⟩
      rw [Set.mem_singleton_iff] at hw
      refine ⟨⟨a, ha⟩, ⟨z, hz⟩, ?_⟩
      rw [← hxz, ← haw, hw]
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
      rw [Set.mem_mul]
      refine ⟨(a : G) * g, ?_, (b : G), hb, rfl⟩
      rw [Set.mem_mul]
      exact ⟨(a : G), ha, g, by simp, rfl⟩
  rw [hset]
  have h := Commons.GroupTheory.Subgroup.card_doubleCoset_mul B g
  rw [h, pow_two]

end Commons.GroupTheory.DoubleCoset