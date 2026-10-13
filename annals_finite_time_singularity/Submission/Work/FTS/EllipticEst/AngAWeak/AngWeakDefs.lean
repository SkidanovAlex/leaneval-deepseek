/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the weak first-order angular slice estimate

This file fixes the objects used to prove

  `Work.FTS.EllipticEst.AngAWeak.weakSliceFirstOrder`:

* `wq q θ = sin(2θ)^{-q}`, the angular weight of the estimate;
* `pE q X = (2q²+q-6)X² + (1-q)X + (2q+5)`, the polynomial in `cos 2θ` describing the
  coefficient `E₁` of the exact integration-by-parts identity
  `(u')²σ = σ·(Lzero1 u)·u + E₁·u² + B'`  (see `sliceId`);
* `Eone q θ = sin(2θ)^{-(2+q)} · pE q (cos 2θ)`;
* `wqD q θ = -2q cos 2θ sin(2θ)^{-(q+1)}`, the derivative of `wq q`;
* `Bfun q u θ = u'uσ - ½u²σ' - ½u² tan θ σ`, the boundary flux of the identity.

The two facts about these objects that the estimate consumes are

* `Eone_le`  : `Eone q θ ≤ 2q(q+1)·sin(2θ)^{-(2+q)} + 6·sin(2θ)^{-q}`,
* `hasDerivAt_Bfun` : the pointwise identity above.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The angular weight `sin(2θ)^{-q}` of the weak first-order slice estimate. -/
def wq (q θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-q)

/-- The derivative of `wq q`:  `-2q cos(2θ) sin(2θ)^{-(q+1)}`. -/
def wqD (q θ : ℝ) : ℝ := -2 * q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(q + 1))

/-- The polynomial `P(X) = (2q²+q-6)X² + (1-q)X + (2q+5)` whose value at `cos 2θ` gives the
coefficient `E₁` of the integration-by-parts identity. -/
def pE (q X : ℝ) : ℝ := (2 * q ^ 2 + q - 6) * X ^ 2 + (1 - q) * X + (2 * q + 5)

/-- `E₁(θ) = sin(2θ)^{-(2+q)}·P(cos 2θ)`, the coefficient of `u²` in the identity
`(u')²σ = σ·(Lzero1 u)·u + E₁·u² + B'`. -/
def Eone (q θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + q)) * pE q (Real.cos (2 * θ))

/-- The boundary flux `B θ = u'θ·u θ·σ θ - ½(u θ)²·σ'θ - ½(u θ)²·tan θ·σ θ` of the identity. -/
def Bfun (q : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv u θ * u θ * wq q θ - (1 / 2) * (u θ) ^ 2 * wqD q θ
    - (1 / 2) * (u θ) ^ 2 * Real.tan θ * wq q θ

/-- On the closed angular interval the sine is nonnegative. -/
lemma wq_sin_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- On the *open* angular interval the sine is positive. -/
lemma wq_sin_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight is nonnegative on `Iθ`. -/
lemma wq_nonneg {q : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wq q θ :=
  Real.rpow_nonneg (wq_sin_nonneg hθ) _

/-- The weight is positive on the open interval. -/
lemma wq_pos {q : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < wq q θ :=
  Real.rpow_pos_of_pos (wq_sin_pos hθ) _

/-- On the open interval the weight is at least `1`. -/
lemma one_le_wq {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ wq q θ := by
  have hpos := wq_sin_pos hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -q ≤ 0)
  simpa [wq, Real.one_rpow] using h

end Work.FTS.EllipticEst.AngAWeak
