import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false

/-!
# `pth (EVzR Y) = EVzD Y` on the open quadrant

`EVzR Y = 2(cos²θ - 2 sin²θ)·Y + sin(2θ)·∂_θY` and `EVzD Y` is its product-rule derivative
(`Flat6Defs`).  The identity is the analytic step of the order-six flat bound `EVz6`: it lets the
consumers transfer a bound on `EVzD Y` to a bound on `∂_θ(EVzR Y)`.

The proof is the product rule.  On the open quadrant the two `θ`-slices `θ' ↦ Y z θ'` and
`θ' ↦ ∂_θY z θ'` are `C^∞` (hence differentiable), and the two coefficient functions
`θ' ↦ cos²θ' - 2 sin²θ'` and `θ' ↦ sin(2θ')` are differentiable; `HasDerivAt.mul` /
`HasDerivAt.const_mul` / `HasDerivAt.add` assemble the derivative of the sum, and
`HasDerivAt.deriv` converts back to the `deriv`-form.  Everything is definitional after
unfolding `EVzD`, `Dth` and `pth`.
-/

theorem PthEVzR (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.FTS.StrongPersist.SP6.EVzR Y) z θ
        = Work.FTS.StrongPersist.SP6.EVzD Y z θ := by
  intro z θ hz hθ hθ2
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  -- the two `θ`-slices of `Y` and of `∂_θY` are differentiable on the open quadrant
  have hYd : DifferentiableAt ℝ (fun θ' : ℝ => Y z θ') θ :=
    ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)
  have hPYd : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ :=
    (((hsm.pth).curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)
  -- the two angular coefficients
  have hcd : DifferentiableAt ℝ (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ := by
    fun_prop
  have hsd : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ := by fun_prop
  have hc : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
      (deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) θ := hcd.hasDerivAt
  have hs : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
      (deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) θ := hsd.hasDerivAt
  have hY : HasDerivAt (fun θ' : ℝ => Y z θ') (deriv (fun θ' : ℝ => Y z θ') θ) θ :=
    hYd.hasDerivAt
  have hP : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Y z θ')
      (deriv (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ) θ := hPYd.hasDerivAt
  -- the two summands of `EVzR Y`
  have hA : HasDerivAt (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) * Y z θ')
      (2 * deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * deriv (fun θ' : ℝ => Y z θ') θ) θ :=
    (hc.const_mul 2).mul hY
  have hB : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * Work.Spaces.pth Y z θ')
      (deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ
        + Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ) θ :=
    hs.mul hP
  have hmain : HasDerivAt (fun θ' : ℝ => Work.FTS.StrongPersist.SP6.EVzR Y z θ')
      (Work.FTS.StrongPersist.SP6.EVzD Y z θ) θ := by
    refine (hA.add hB).congr_deriv ?_
    simp only [Work.FTS.StrongPersist.SP6.EVzD, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  show deriv (fun θ' : ℝ => Work.FTS.StrongPersist.SP6.EVzR Y z θ') θ
    = Work.FTS.StrongPersist.SP6.EVzD Y z θ
  exact hmain.deriv

end Work.FTS.StrongPersist.SP6
