import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Group

/-- A nontrivial finite `2`-group has a central element of order `2`.

The center of a nontrivial finite `p`-group is nontrivial, and (being a subgroup)
is again a `p`-group; Cauchy's theorem then produces an element of order `p`
inside it, which is central. -/
theorem central_involution_of_isPGroup {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hnt : Nontrivial P) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial P := hnt
  haveI hZ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨g, hg1⟩ := exists_ne (1 : Subgroup.center P)
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) :=
    ((hP.to_subgroup (Subgroup.center P)).dvd_orderOf hg1).trans (orderOf_dvd_natCard g)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdvd
  exact ⟨(z : P), z.2, by rw [Subgroup.orderOf_coe, hz]⟩

end Work.BrauerSuzuki.Group
