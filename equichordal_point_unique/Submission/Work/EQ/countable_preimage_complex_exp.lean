import Mathlib

/-!
# Countability of `Complex.exp ⁻¹' P` for countable `P`

The complex exponential is a countable-to-one covering map: over every point
`w ≠ 0` the fibre is the `ℤ`-orbit `w ↦ log w + n * (2πI)` (`Complex.log_exp_exists`,
`Complex.exp_eq_exp_iff_exists_int`), and `0` has empty fibre.  Equivalently the
exponential is a countable-to-one map, so it pulls countable sets back to
countable sets.  Mathlib packages exactly this as `Complex.countable_preimage_exp`,
which we invoke here.
-/

namespace Work.EQ

theorem countable_preimage_complex_exp {P : Set ℂ} (hP : P.Countable) :
    (Complex.exp ⁻¹' P).Countable := by
  -- The exponential is countable-to-one: `(exp ⁻¹' s).Countable ↔ s.Countable`.
  exact Complex.countable_preimage_exp.mpr hP

end Work.EQ
