import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

/-- The fixed points of an endomorphism `f` of a finite abelian group `V` are exactly the
elements of `LinearMap.ker (f - 1)`; discarding the zero vector therefore leaves
`Nat.card (LinearMap.ker (f - 1)) - 1` nonzero fixed points. -/
theorem natCard_fixed_pts {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : V →ₗ[ZMod 2] V) :
    Nat.card {x : V // x ≠ 0 ∧ f x = x} = Nat.card (LinearMap.ker (f - 1)) - 1 := by
  -- The nonzero fixed points are precisely `ker (f - 1)` with the zero vector removed.
  have hset : {x : V | x ≠ 0 ∧ f x = x} = (LinearMap.ker (f - 1) : Set V) \ {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
      LinearMap.mem_ker, LinearMap.sub_apply]
    simp only [Module.End.one_apply, sub_eq_zero, ne_eq]
    tauto
  -- `Nat.card` of a subtype is the `Set.ncard` of the corresponding set.
  rw [show Nat.card {x : V // x ≠ 0 ∧ f x = x} =
        ({x : V | x ≠ 0 ∧ f x = x} : Set V).ncard from rfl, hset]
  -- Removing a single (existing) element lowers the cardinality by one.
  rw [Set.ncard_sdiff_singleton_of_mem
    (show (0 : V) ∈ (LinearMap.ker (f - 1) : Set V) by simp)]
  -- `↑(LinearMap.ker (f - 1))` as a set and as a type have the same `Nat.card` (by definition).
  rfl

end Work.Hering.Wagner
