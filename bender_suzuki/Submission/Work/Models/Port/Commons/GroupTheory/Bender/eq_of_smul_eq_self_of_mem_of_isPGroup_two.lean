import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Bender

/-- The set of points fixed by a nontrivial `2`-subgroup `P` is a single point: any point `x`
fixed by a nontrivial element `u` of `P` is already fixed by all of `P`.

Indeed `Q := Stab_G(x) ⊓ P` is a nontrivial `2`-subgroup (it contains `u`), and both `x`
and `z` are common fixed points of `Q`; by uniqueness of the common fixed point of a
nontrivial `2`-subgroup (`existsUnique_fixedPoint_isPGroup_two`) they coincide. -/
theorem eq_of_smul_eq_self_of_mem_of_isPGroup_two {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω] (heven : Even (Nat.card G))
    (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x)
    {P : Subgroup G} (hP : IsPGroup 2 P) {z : Ω} (hz : ∀ g : P, (g : G) • z = z)
    {u : G} (hu : u ∈ P) (hu1 : u ≠ 1) {x : Ω} (hx : u • x = x) : x = z := by
  classical
  -- The stabilizer of `x` intersected with `P` is a nontrivial `2`-subgroup.
  set Q : Subgroup G := (MulAction.stabilizer G x) ⊓ P with hQ
  have huQ : u ∈ Q := ⟨hx, hu⟩
  have hQle : Q ≤ P := by rw [hQ]; exact inf_le_right
  have hQne : Q ≠ ⊥ := by
    intro h
    have hbot : u ∈ (⊥ : Subgroup G) := h ▸ huQ
    rw [Subgroup.mem_bot] at hbot
    exact hu1 hbot
  have hQ2 : IsPGroup 2 Q :=
    hP.of_injective (Subgroup.inclusion hQle) (Subgroup.inclusion_injective hQle)
  -- Uniqueness of the common fixed point of `Q`.
  obtain ⟨a, -, huniq⟩ := existsUnique_fixedPoint_isPGroup_two heven hinv Q hQ2 hQne
  have hxz : x = a := huniq x (fun g => g.2.1)
  have hzz : z = a := huniq z (fun g => hz ⟨(g : Q).val, g.2.2⟩)
  exact hxz.trans hzz.symm

end Commons.GroupTheory.Bender
