import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial

namespace Work.Genus.Order

/-- **Differentiating a polynomial lowers the multiplicity of an irreducible factor by at most
one.**  For an irreducible `π ∈ F[X]` and a polynomial `g` with non-zero derivative,
`multiplicity π g.derivative ≥ multiplicity π g - 1` (an inequality in `ℤ`).  Route:
`pow_multiplicity_dvd π g` gives `π ^ multiplicity π g ∣ g`, and Mathlib's
`pow_sub_one_dvd_derivative_of_pow_dvd` turns this into `π ^ (multiplicity π g - 1) ∣ g.derivative`;
since `g.derivative ≠ 0` and `π` is a non-unit, the multiplicity of `π` in `g.derivative` is finite
(`FiniteMultiplicity.of_not_isUnit`), so `FiniteMultiplicity.le_multiplicity_of_pow_dvd` gives the
`ℕ`-inequality, which is pushed to `ℤ` (case split on whether `multiplicity π g` is `0`, then
`Nat.cast_sub` / `omega`).  Note `g ≠ 0` is automatic from `g.derivative ≠ 0`, and in
characteristic `p` the hypothesis `g.derivative ≠ 0` cannot be dropped (`g = X ^ p` in `𝔽_p[X]`
has `multiplicity X g = p` but `g.derivative = 0`). -/
lemma multiplicity_derivative_ge {F : Type*} [Field F] {π g : Polynomial F} (hπ : Irreducible π)
    (hg' : g.derivative ≠ 0) :
    (multiplicity π g : ℤ) - 1 ≤ (multiplicity π g.derivative : ℤ) := by
  have hfin : FiniteMultiplicity π g.derivative :=
    FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hg'
  have hle : multiplicity π g - 1 ≤ multiplicity π g.derivative :=
    hfin.le_multiplicity_of_pow_dvd
      (pow_sub_one_dvd_derivative_of_pow_dvd (pow_multiplicity_dvd π g))
  rcases eq_or_ne (multiplicity π g) 0 with h0 | h0
  · have : (0 : ℤ) ≤ (multiplicity π g.derivative : ℤ) := by exact_mod_cast Nat.zero_le _
    omega
  · have h1 : 1 ≤ multiplicity π g := Nat.one_le_iff_ne_zero.mpr h0
    have hcast : ((multiplicity π g - 1 : ℕ) : ℤ) ≤ (multiplicity π g.derivative : ℤ) := by
      exact_mod_cast hle
    rw [Nat.cast_sub h1] at hcast
    exact hcast

end Work.Genus.Order
