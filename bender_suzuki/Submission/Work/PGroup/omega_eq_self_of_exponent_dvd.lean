import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- If the exponent of `P` divides `p ^ i`, then every element `x` of `P` satisfies
`x ^ (p ^ i) = 1` by `Monoid.exponent_dvd_iff_forall_pow_eq_one`, so `x` is one of the generators
of `Ωᵢ(P)`.  Since `Ωᵢ(P) ≤ P` holds by construction (`Work.PGroup.omega_le`), this gives
`Ωᵢ(P) = P`. -/
theorem omega_eq_self_of_exponent_dvd {G : Type*} [Group G] {p i : ℕ} (P : Subgroup G)
    (h : Monoid.exponent P ∣ p ^ i) : Work.PGroup.omega p i P = P := by
  refine le_antisymm (omega_le p i P) fun x hx => ?_
  have hx1 : x ^ (p ^ i) = 1 := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h (⟨x, hx⟩ : P)
    simpa using hh
  exact subset_omega hx hx1

end Work.PGroup
