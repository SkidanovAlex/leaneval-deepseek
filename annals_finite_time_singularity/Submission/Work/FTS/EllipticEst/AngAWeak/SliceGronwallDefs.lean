/-
Copyright: work module for the Elgindi finite-time singularity project.

# Primitives for the slice Gronwall estimate (`sliceGronwallLeft`)

The target `Work.FTS.EllipticEst.AngAWeak.sliceGronwallLeft` states that a function
`u : ℝ → ℝ` which is `C^∞` on the open angular interval `(0, π/2)` and whose angular
operator `Lzero1 u = -u'' + (u·tan)' - 6u` has square-integrable values on `(0, π/4)`
is bounded, together with its derivative, on `(0, π/4)`.

The proof is a Gronwall argument for the quadratic energy

  `Fsq u θ = (u θ)^2 + (deriv u θ)^2`

of the *first-order system* associated with the equation `Lzero1 u = g`.  Two facts are
needed:

* the pointwise differential inequality `|(Fsq u)'| ≤ 8·Fsq u + (Lzero1 u)^2` on
  `(0, π/4)` — this is `sliceGronwallPointwise` (the coefficients `tan θ` and
  `2/(1+cos 2θ) - 6` of the ODE are bounded by `1` and `6` there);
* the integral form of Gronwall's inequality — `gronwallIntegralOn`.

This module collects the definition of `Fsq` and the elementary interval facts (positivity
of `cos 2θ`, bounds for `tan θ` and for `2/(1+cos 2θ)`) that both facts use.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The quadratic energy `u θ ^ 2 + (deriv u θ) ^ 2` of the one-dimensional slice. -/
def Fsq (u : ℝ → ℝ) (θ : ℝ) : ℝ := (u θ) ^ 2 + (deriv u θ) ^ 2

/-- The slice energy is nonnegative. -/
lemma Fsq_nonneg (u : ℝ → ℝ) (θ : ℝ) : 0 ≤ Fsq u θ := by
  rw [Fsq]; positivity

/-- `u θ ^ 2 ≤ Fsq u θ`. -/
lemma sq_le_Fsq_left (u : ℝ → ℝ) (θ : ℝ) : (u θ) ^ 2 ≤ Fsq u θ := by
  rw [Fsq]; nlinarith [sq_nonneg (deriv u θ)]

/-- `(deriv u θ) ^ 2 ≤ Fsq u θ`. -/
lemma sq_le_Fsq_right (u : ℝ → ℝ) (θ : ℝ) : (deriv u θ) ^ 2 ≤ Fsq u θ := by
  rw [Fsq]; nlinarith [sq_nonneg (u θ)]

/-- On `(0, π/4)` the cosine of the doubled angle is positive. -/
lemma cos_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    0 < Real.cos (2 * θ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- On `(0, π/4)` the cosine of the doubled angle is at most `1`. -/
lemma cos_two_le_one (θ : ℝ) : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one _

/-- On `(0, π/4)` the denominator `1 + cos 2θ` is positive. -/
lemma one_add_cos_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    0 < 1 + Real.cos (2 * θ) := by
  have := cos_two_pos_of_mem_Ioo hθ
  linarith

/-- On `(0, π/4)` the `θ`-tangent is bounded by `1` in absolute value. -/
lemma abs_tan_le_one_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    |Real.tan θ| ≤ 1 := by
  have hmem₀ : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmemθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hmem₁ : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hlt : Real.tan θ < Real.tan (Real.pi / 4) :=
    Real.strictMonoOn_tan hmemθ hmem₁ hθ.2
  have hge : Real.tan 0 ≤ Real.tan θ :=
    (Real.strictMonoOn_tan.monotoneOn hmem₀ hmemθ hθ.1.le)
  rw [Real.tan_pi_div_four] at hlt
  rw [Real.tan_zero] at hge
  rw [abs_le]
  exact ⟨by linarith, hlt.le⟩

/-- On `(0, π/4)` the coefficient `2/(1+cos 2θ) - 5` is bounded by `5` in absolute value. -/
lemma abs_two_div_one_add_cos_two_sub_five_le {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    |2 / (1 + Real.cos (2 * θ)) - 5| ≤ 5 := by
  have hpos := one_add_cos_two_pos hθ
  have hle : Real.cos (2 * θ) ≤ 1 := cos_two_le_one θ
  have hcp := cos_two_pos_of_mem_Ioo hθ
  have hnn : 0 ≤ 2 / (1 + Real.cos (2 * θ)) := by positivity
  have hbound : 2 / (1 + Real.cos (2 * θ)) ≤ 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end Work.FTS.EllipticEst.AngAWeak
