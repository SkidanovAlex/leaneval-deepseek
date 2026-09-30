import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The finite product `∏ᶠ i ∈ s, f i` over a set `s` that carries a `Fintype` instance equals the
product over the subtype `s`. (Mathlib has this split into `finprod_mem_eq_toFinset_prod` and
`Finset.prod_set_coe`; this packages it.) -/
theorem finprod_mem_eq_fintype_prod {α M : Type*} [CommMonoid M] (s : Set α) [Fintype s]
    (f : α → M) : ∏ᶠ i ∈ s, f i = ∏ i : s, f i := by
  rw [finprod_mem_eq_toFinset_prod]
  exact (Finset.prod_set_coe (f := f) s).symm

end Work.BW
