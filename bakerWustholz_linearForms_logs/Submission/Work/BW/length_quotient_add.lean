import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Third-isomorphism additivity of `Module.length`.** For submodules `p ≤ q` of an
`R`-module `M`, `length (M ⧸ p) = length (M ⧸ q) + length (q ⧸ p)`. Route: the natural maps
`q ⧸ p.comap q.subtype →ₗ M ⧸ p →ₗ M ⧸ q` (induced by `q.subtype` and `LinearMap.id`) form a
short exact sequence; apply `Module.length_eq_add_of_exact` (`Submodule.mapQ`, `Submodule.ker_mapQ`,
`Submodule.range_mapQ`). -/
theorem length_quotient_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) (h : p ≤ q) :
    Module.length R (M ⧸ p) = Module.length R (M ⧸ q) + Module.length R (q ⧸ p.comap q.subtype) := by
  -- View `p` inside `q` by pulling it back along the inclusion `q.subtype ↪ M`.
  let p' : Submodule R q := p.comap q.subtype
  -- The inclusion-induced map `q ⧸ p' →ₗ M ⧸ p`.
  have hker : LinearMap.ker (p'.mapQ p q.subtype le_rfl) = ⊥ := by
    rw [Submodule.ker_mapQ]
    exact Submodule.mkQ_map_self p'
  have hinj : Function.Injective (p'.mapQ p q.subtype le_rfl) :=
    LinearMap.ker_eq_bot.mp hker
  -- The natural surjection `M ⧸ p →ₗ M ⧸ q`.
  have hsurj : Function.Surjective (Submodule.factor h) := Submodule.factor_surjective h
  -- The two maps form a short exact sequence in the middle term `M ⧸ p`.
  have hexact : Function.Exact (p'.mapQ p q.subtype le_rfl) (Submodule.factor h) := by
    rw [LinearMap.exact_iff]
    rw [Submodule.ker_mapQ]
    rw [Submodule.range_mapQ]
    simp
  have key :=
    Module.length_eq_add_of_exact (p'.mapQ p q.subtype le_rfl) (Submodule.factor h)
      hinj hsurj hexact
  rw [key, add_comm]

end Work.BW
