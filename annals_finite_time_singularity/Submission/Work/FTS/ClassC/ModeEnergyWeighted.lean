/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/ModeEnergyWeighted` — the per-mode weighted energy identity

For a solution `a` of the mode-`m` radial problem

  `-α²z²a'' - α(5+α)za' + λ a = c`   on `(0,∞)`

with the decay and the boundary conditions that make the integration by parts legitimate,

  `α²∫_0^∞ (z a')² w²  +  (λ - 3α² - 3α(5+α)/2) ∫_0^∞ a² w²  ≤  ∫_0^∞ c a w²`,

where `w(z) = (1+z)²/z²` is the paper's radial weight.  This is Step 1 of the proof of
Proposition `prop:H2` of Elgindi (Annals 194 (2021)), *specialised to a single mode*, which is
what makes the constant explicit in `λ`:

* the two `w²`-derivative bounds `|(z²w²)''| ≤ 6w²`, `|(z w²)'| ≤ 3w²` (the paper's "it can be
  checked directly"), giving the coercive coefficient `λ - 3α² - 3α(5+α)/2 ≥ 14 - 3α² - 3α(5+α)/2`;
* **no Fourier step and no use of the angular moment condition**: for `m ≥ 1` the eigenvalue
  `λ = λ_m = 2m(2m+5)` already exceeds the loss, so the inequality holds for the *whole* mode,
  uniformly in `m`.

Consequence (see `ModeEnergyBounds`): `‖a‖_{w²} ≤ ‖c‖_{w²} / (λ - 3α² - 3α(5+α)/2)`, i.e. a
*sharp per-mode* bound with an explicit `λ_m⁻¹` gain — the input of the mode-summability route to
the level-`0` honesty of the elliptic existence node.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.ModeEnergyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The integrand of the per-mode weighted energy identity: `flux` (see `ModeEnergyDefs`) is a
primitive of it, along the mode ODE. -/
def enInt (α lam : ℝ) (a c : ℝ → ℝ) (z : ℝ) : ℝ :=
  α ^ 2 * rw z * (deriv a z) ^ 2 - (α ^ 2 / 2) * rwbb z * (a z) ^ 2
    + ((α * (5 + α)) / 2) * rwc z * (a z) ^ 2 + lam * (a z) ^ 2 * (Work.Spaces.w z) ^ 2
    - c z * a z * (Work.Spaces.w z) ^ 2

/-- **The pointwise identity**: along the mode ODE, `flux α a` has derivative `enInt α lam a c`. -/
theorem hasDerivAt_flux {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (ha : HasDerivAt a (deriv a z) z)
    (ha' : HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
      = lam * a z - c z) :
    HasDerivAt (flux α a) (enInt α lam a c z) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 := (hasDerivAt_rw hz0).mul (ha'.mul ha)
  have h2 := (hasDerivAt_rwb hz0).mul (ha.pow 2)
  have h3 := (hasDerivAt_rwDiv hz0).mul (ha.pow 2)
  have hmain := ((h1.const_mul (α ^ 2)).sub (h2.const_mul (α ^ 2 / 2))).add
    (h3.const_mul ((α * (5 + α)) / 2))
  convert hmain using 1
  · -- the two functions agree
    funext t
    simp only [flux, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
    ring_nf
  · -- the two derivative values agree
    have hDa : deriv (deriv a) z
        = (lam * a z - c z - α * (5 + α) * z * deriv a z) / (α ^ 2 * z ^ 2) := by
      rw [eq_div_iff (by positivity)]
      linarith [hode]
    rw [hDa]
    simp only [enInt, rw, rwb, rwbb, rwc, Work.Spaces.w, Pi.pow_apply, Pi.mul_apply,
      Pi.div_apply]
    field_simp
    ring

end Work.FTS.ClassC
