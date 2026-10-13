import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I4G Φ` is differentiable (with derivative `deriv (I4G Φ)`) on `(0, π/2)`

The boundary primitive

`I4G Φ θ = ½ · (sin θ / cos³θ) · σ θ · (cos²θ · (Φ/cos)'θ)²`

of the honest `I₄` upper bound is a finite product of functions each of which is
differentiable at every `θ ∈ (0, π/2)`, provided `Φ` is of class `C²` on that interval:

* `½` and `sin θ / cos³θ` are smooth (and `cos θ ≠ 0` on the interval),
* `σ θ = sin(2θ)^{-99/100}` is differentiable because `sin(2θ) > 0` there,
* `cos²θ` is smooth and `(Φ/cos)'` is differentiable at `θ` because `Φ/cos` is `C²` there
  (`C²` at a point ⟹ `deriv` is `C¹` at that point ⟹ differentiable).

Since differentiability at `θ` already says `HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ`, the
claim follows.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- `Φ/cos` is `C²` at every interior point of `(0, π/2)`. -/
private lemma contDiffAt_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ 2 (I4psi Φ) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hcd : ContDiffAt ℝ 2 Φ θ := hsm.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  change ContDiffAt ℝ 2 (fun θ : ℝ => Φ θ / Real.cos θ) θ
  exact hcd.div (by fun_prop) hcos

/-- The derivative of `Φ/cos`, i.e. the inner factor of `P`, is differentiable at every
interior point. -/
private lemma differentiableAt_deriv_I4psi (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (deriv (I4psi Φ)) θ := by
  have hq : ContDiffAt ℝ 2 (I4psi Φ) θ := contDiffAt_I4psi Φ hsm hθ
  have h1 : ContDiffAt ℝ 1 (deriv (I4psi Φ)) θ := hq.derivWithin (m := 1) (by norm_num)
  exact h1.differentiableAt (by norm_num)

/-- `P = cos²θ · (Φ/cos)'` is differentiable at every interior point. -/
private lemma differentiableAt_I4P (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (I4P Φ) θ := by
  have hcos2 : DifferentiableAt ℝ (fun θ : ℝ => (Real.cos θ) ^ 2) θ := by fun_prop
  have hd : DifferentiableAt ℝ (deriv (I4psi Φ)) θ := differentiableAt_deriv_I4psi Φ hsm hθ
  change DifferentiableAt ℝ (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (I4psi Φ) θ) θ
  exact hcos2.mul hd

/-- `σ θ = sin(2θ)^{-99/100}` is differentiable at every interior point. -/
private lemma differentiableAt_I4sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ I4sig θ := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
  exact h1.rpow_const (Or.inl (ne_of_gt hsin2))

/-- `sin θ / cos³θ` is differentiable at every interior point. -/
private lemma differentiableAt_sin_div_cos_cube {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ : ℝ => Real.sin θ / (Real.cos θ) ^ 3) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : DifferentiableAt ℝ Real.sin θ := by fun_prop
  have hcosd : DifferentiableAt ℝ Real.cos θ := by fun_prop
  exact hsin.div (hcosd.pow 3) (pow_ne_zero 3 hcos)

/-- `I4G Φ` is differentiable at every interior point. -/
private lemma differentiableAt_I4G (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (I4G Φ) θ := by
  change DifferentiableAt ℝ (fun θ : ℝ => (1 / 2) * (Real.sin θ / (Real.cos θ) ^ 3)
    * I4sig θ * (I4P Φ θ) ^ 2) θ
  exact DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul (by fun_prop) (differentiableAt_sin_div_cos_cube hθ))
    (differentiableAt_I4sig hθ)) ((differentiableAt_I4P Φ hsm hθ).pow 2)

theorem I4GHasDerivAt (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ := by
  intro θ hθ
  exact (differentiableAt_I4G Φ hsm hθ).hasDerivAt

end Work.FTS.EllipticEst.Honest
