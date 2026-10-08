import Mathlib.GroupTheory.PGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.GroupTheory.Bender

/-- A nontrivial finite `2`-group has a central element of order `2`. -/
lemma isPGroup_two_exists_center_involution {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P) : ∃ z : Subgroup.center P, orderOf z = 2 := by
  have hcP : IsPGroup 2 (Subgroup.center P) := hP.to_subgroup (Subgroup.center P)
  obtain ⟨n, hn0, hn⟩ := hcP.nontrivial_iff_card.mp (hP.center_nontrivial)
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rw [hn]
    exact dvd_pow_self 2 (ne_of_gt hn0)
  exact exists_prime_orderOf_dvd_card' 2 hdvd

/-- If a finite group acts on a finite set so that every involution fixes a unique point,
then so does every nontrivial `2`-subgroup: it fixes a unique point of the set.

The central involution of the `2`-subgroup (which exists because a nontrivial finite
`2`-group has nontrivial center) fixes a unique point `a`; being central, it forces
every element of the subgroup to fix `a` as well, while uniqueness follows from that of
any single involution of the subgroup. -/
theorem existsUnique_fixedPoint_isPGroup_two {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] (heven : Even (Nat.card G))
    (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    ∃! x : Ω, ∀ g : P, (g : G) • x = x := by
  haveI hntP : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨z, hz⟩ := isPGroup_two_exists_center_involution hP
  have hzG : orderOf ((z : P) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  obtain ⟨a, ha, huniq⟩ := hinv ((z : P) : G) hzG
  refine ⟨a, ?_, ?_⟩
  · intro g
    apply huniq
    have hcommP : (g : P) * (z : P) = (z : P) * (g : P) := (Subgroup.mem_center_iff.mp z.2) g
    have hcommG : ((z : P) : G) * ((g : P) : G) = ((g : P) : G) * ((z : P) : G) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcommP]
    calc ((z : P) : G) • (((g : P) : G) • a)
        = (((z : P) : G) * ((g : P) : G)) • a := by rw [mul_smul]
      _ = (((g : P) : G) * ((z : P) : G)) • a := by rw [hcommG]
      _ = ((g : P) : G) • (((z : P) : G) • a) := by rw [mul_smul]
      _ = ((g : P) : G) • a := by rw [ha]
  · intro y hy
    exact huniq y (hy (z : P))

end Commons.GroupTheory.Bender