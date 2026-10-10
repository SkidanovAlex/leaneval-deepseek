import Mathlib.Analysis.Complex.Polynomial.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- The group of units of `ℂ` is divisible: every element is a `p`-th power.
This is the concrete input from algebraic closedness of `ℂ`. -/
theorem exists_pow_eq_complex_units (p : ℕ) [Fact p.Prime] (u : ℂˣ) :
    ∃ c : ℂˣ, c ^ p = u := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℂ) hp
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne'] at hz
    exact u.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  simp [hz]

end Work.SSGRoute
