import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

/-- If a group `G` acts on `Ω` in such a way that any ordered pair of distinct
points can be carried to any other ordered pair of distinct points (i.e. the
action is doubly transitive, stated without the `IsMultiplyPretransitive`
typeclass), then for any point `a` whose orbit is not a singleton the point
stabiliser `Gₐ` is a coatom of the subgroup lattice of `G`, i.e. a maximal
proper subgroup (Wielandt, th. 7.5). -/
theorem isCoatom_stabilizer_of_forall_pair {G Ω : Type*} [Group G] [MulAction G Ω] (h : ∀ p q r s : Ω, p ≠ q → r ≠ s → ∃ g : G, g • p = r ∧ g • q = s) (a : Ω) (hne : ∃ b : Ω, b ≠ a) : IsCoatom (MulAction.stabilizer G a) := by
  -- Turn the explicit double-transitivity hypothesis into the typeclass form.
  have h2 : MulAction.IsMultiplyPretransitive G Ω 2 :=
    MulAction.is_two_pretransitive_iff.mpr (fun {p q r s} hpq hrs => h p q r s hpq hrs)
  -- A `2`-transitive action is primitive, and in a primitive action the
  -- stabiliser of a point is a maximal subgroup.
  have hpp : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  -- `Nontrivial Ω` from the existence of a point different from `a`.
  have hnt : Nontrivial Ω := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, a, hb⟩
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) a

end Commons.GroupTheory.GroupAction