/-
Copyright (c) 2024. All rights reserved.

# Squares are central in a class-two group whose commutators are involutions

`Work.Higman.Q3.sq_mem_center_of_class_two`: if `G` has class at most two
(`⁅⊤,⊤⁆ ≤ Z(G)`) and every commutator is an involution (`⁅x,y⁆ ^ 2 = 1`), then the square of
every element is central.

This is the general form of the class-two computation used for Suzuki 2-groups: the identity
`⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2` (`Work.Higman.commutator_sq_eq`, which only needs centrality of the
commutators) collapses to `1`.

Its role in the `C₄` exclusion: if `E` is a subgroup of a Suzuki 2-group `P` with
`E' = Ω₁(E) = Z(E)` (so that `E` is of class two and every commutator of `E` is an involution),
then every square of `E` lies in `Z(E) = Ω₁(E)` — which kills the configuration
`E² = A ⊋ A² = E'`.
-/

import Submission.Work.Higman.OmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.Q3

/-- In a group of class at most two whose commutators are all involutions, every square is
central. -/
theorem sq_mem_center_of_class_two {G : Type} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G)
    (h2 : ∀ x y : G, (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) :
    ∀ x : G, x ^ 2 ∈ Subgroup.center G := by
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : ⁅x ^ 2, y⁆ = 1 := by
    rw [← Work.Higman.commutator_sq_eq hZ x y, commutatorElement_def]
    exact h2 x y
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end Work.Higman.Q3
