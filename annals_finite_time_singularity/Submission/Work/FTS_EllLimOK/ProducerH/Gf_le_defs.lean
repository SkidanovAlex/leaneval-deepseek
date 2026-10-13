import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Tonelli kernel of the `Gf` bound — definitions

This module fixes the vocabulary for the global bound on the radial density
`Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` (with `M₁ = mom U`, `β = beta α`).

The proof substitutes `t = zv` in the inner integral (`mom_subst`) and then applies Tonelli to the
product `(0,∞) × (0,∞)`, with the `t`-variable as the *outer* one.  The joint kernel of that
Tonelli step is naturally split into three factors:

* `GfPhi α U t = |t|^{β+4} A(t) / (1+t)^4`, with `A = mass α U` — the `t`-factor.  On `t > 0` it
  equals `t^β · M₁(t)` (`mass_eq_w2_mom` + `w_sq_mul_z4`), and it is nonnegative everywhere
  (the `|·|` is only there to make the nonnegativity global; for `t > 0` it is the plain power);
* `GfZeta α z = w(z)² |z|^{-(β+1)}` — the `z`-factor;
* `GfKer α U t z = 1_{t<z} · GfZeta α z · GfPhi α U t` — the joint kernel.

For `z > 0`, `z ↦ ∫ₜ GfKer α U t z` is exactly `Gf α U z`; for `t > 0`,
`t ↦ ∫_z GfKer α U t z ≤ A(t)/β`.  Both facts are the content of the pieces of the `Gf_le` proof.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- The `t`-factor `φ(t) = |t|^{β+4} A(t)/(1+t)^4` of the Tonelli kernel, where `A = mass α U`. -/
def GfPhi (α : ℝ) (U : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  |t| ^ (beta α + 4) * mass α U t / (1 + t) ^ 4

/-- The `z`-factor `ζ(z) = w(z)² |z|^{-(β+1)}` of the Tonelli kernel. -/
def GfZeta (α : ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * |z| ^ (-(beta α + 1))

/-- The joint Tonelli kernel `1_{t<z} · ζ(z) · φ(t)`. -/
def GfKer (α : ℝ) (U : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ :=
  (if t < z then 1 else 0) * GfZeta α z * GfPhi α U t

theorem GfPhi_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ GfPhi α U t := by
  have h1 : 0 ≤ |t| ^ (beta α + 4) := Real.rpow_nonneg (abs_nonneg t) _
  have h2 : 0 ≤ mass α U t := mass_nonneg α U t
  have h3 : 0 ≤ (1 + t) ^ 4 := by positivity
  unfold GfPhi
  exact div_nonneg (mul_nonneg h1 h2) h3

theorem GfZeta_nonneg (α : ℝ) (z : ℝ) : 0 ≤ GfZeta α z := by
  have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ |z| ^ (-(beta α + 1)) := Real.rpow_nonneg (abs_nonneg z) _
  unfold GfZeta
  positivity

theorem GfKer_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (t z : ℝ) : 0 ≤ GfKer α U t z := by
  have h1 : (0 : ℝ) ≤ (if t < z then 1 else 0) := by split <;> norm_num
  unfold GfKer
  exact mul_nonneg (mul_nonneg h1 (GfZeta_nonneg α z)) (GfPhi_nonneg α U t)

/-- On `t > 0` the `t`-factor is the plain power times the mass. -/
theorem GfPhi_eq_of_pos (α : ℝ) (U : ℝ → ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    GfPhi α U t = t ^ (beta α + 4) * mass α U t / (1 + t) ^ 4 := by
  unfold GfPhi
  rw [abs_of_pos ht]

/-- `β = 3/α - 1` is positive (indeed `≥ 2`) for `0 < α ≤ 1`. -/
theorem beta_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < beta α := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hdiv : 3 ≤ 3 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  unfold beta
  linarith

end Work.FTS_EllLimOK.ProducerH
