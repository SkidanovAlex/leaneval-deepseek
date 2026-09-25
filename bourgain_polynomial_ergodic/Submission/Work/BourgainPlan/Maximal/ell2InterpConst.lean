import Mathlib

/-!
# The interpolation constant used by the `ℓ²`-valued dyadic maximal inequality

This tiny module only records the *explicit* constant `marcConst p A₀ A₁` produced by the
Marcinkiewicz interpolation between the weak-`(1,1)` bound (constant `A₀`) and the strong-`(2,2)`
bound (constant `A₁`) of the `ℓ²`-valued dyadic maximal operator, in the `∫⁻`-form

`∫⁻ (T f)^p ≤ ofReal (marcConst p A₀ A₁) * ∫⁻ ‖f‖^p`   `(1 < p < 2)`.

It is the constant of `Work.BourgainPlan.Maximal.lintegral_rpow_le_of_weak_one_l2`
(`Bc(p) = 12·2^{p-1}/(p-1) + 16/(2-p)`, times `A₀^{2-p} A₁^{2p-2}`).  Keeping it in a separate
module makes it possible to state the (abstract) interpolation lemma with a constant that is
*independent of the ambient types*, so that it can be reused uniformly for every number `n` of
components in `ell2MaxLpLtTwo`.
-/

namespace Work.BourgainPlan.Maximal

/-- The Marcinkiewicz constant for `weak-(1,1)` (constant `A0`) plus `strong-(2,2)`
(constant `A1`), in the `∫⁻`-form with exponent `p`. -/
noncomputable def marcConst (p A0 A1 : ℝ) : ℝ :=
  (12 * (2 : ℝ) ^ (p - 1) / (p - 1) + 16 / (2 - p)) * A0 ^ (2 - p) * A1 ^ (2 * p - 2)

end Work.BourgainPlan.Maximal
