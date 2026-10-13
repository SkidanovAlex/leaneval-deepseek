import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
Copyright: work module for the Elgindi finite-time singularity project.

# `GsrcPthTwo`: the second `θ`-derivative of the angular source

`Mine.Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` is the angular source of the equation
(PolarBSL).  The two top-slot estimates of the elliptic chapter need its iterated
`∂_θ`-derivatives, expanded over the three summands: this file proves the order-`1` and
order-`2` cases

  `∂_θ (Gsrc α F Ψ)   = ∂_θ F   + α² ∂_θ (z²∂_z²Ψ) + α(5+α) ∂_θ (D_zΨ)`,
  `∂_θ²(Gsrc α F Ψ)   = ∂_θ²F   + α² ∂_θ²(z²∂_z²Ψ) + α(5+α) ∂_θ²(D_zΨ)`

on the open quadrant `Q0 = (0,∞) × (0,π/2)`, for `SmoothOpen F` and `SmoothOpen Ψ`.

The mathematical content is only the linearity of `∂_θᵏ` over a *three-term* linear
combination.  The proof tool is the induction `pthIter_three_lin` below: since `deriv` is
totalised, the identity is claimed only where all three summands are differentiable in
`θ`, which `SmoothOpen` (i.e. `C^∞` on the open quadrant) supplies through the slices
(`SmoothOpen.curry_θ`), and the induction is carried by `Filter.EventuallyEq.deriv_eq`
along with `deriv`-additivity on the three differentiable slices.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SrcBnd

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary `∂_θ`-calculus on the open quadrant -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The `θ`-slice of a `∂_θ`-iterate of a `SmoothOpen` function is differentiable at every
interior angle. -/
theorem differentiableAt_slice_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter i F z θ') θ :=
  (((smoothOpen_pthIter hF i).curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- **Three-term `∂_θ`-linearity.**  On the open quadrant the iterated `∂_θ`-derivative of a
linear combination `f + a·g + b·h` of three `C^∞` functions is the corresponding combination
of the iterated derivatives. -/
theorem pthIter_three_lin {f g h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h)
    (a b : ℝ) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.pthIter i (fun z t => f z t + a * g z t + b * h z t) z θ
        = Work.Spaces.pthIter i f z θ + a * Work.Spaces.pthIter i g z θ
          + b * Work.Spaces.pthIter i h z θ := by
  induction i with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
      intro z θ hz hθ
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n
            (fun z t => f z t + a * g z t + b * h z t) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + a * Work.Spaces.pthIter n g z θ'
            + b * Work.Spaces.pthIter n h z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'
      have hdA := differentiableAt_slice_pthIter hf n hz hθ
      have hdB := differentiableAt_slice_pthIter hg n hz hθ
      have hdC := differentiableAt_slice_pthIter hh n hz hθ
      have hp : HasDerivAt (fun θ' : ℝ => Work.Spaces.pthIter n f z θ'
            + a * Work.Spaces.pthIter n g z θ' + b * Work.Spaces.pthIter n h z θ')
          (deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ
            + a * deriv (fun θ' : ℝ => Work.Spaces.pthIter n g z θ') θ
            + b * deriv (fun θ' : ℝ => Work.Spaces.pthIter n h z θ') θ) θ :=
        ((hdA.hasDerivAt.add (hdB.hasDerivAt.const_mul a)).add
          (hdC.hasDerivAt.const_mul b))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      rw [heq.deriv_eq]
      exact hp.deriv

/-- Multiplication of a `SmoothOpen` function by the radial factor `z²`. -/
theorem smoothOpen_zsq_mul (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * G z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * G z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2 * G p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul
    (show ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => G p.1 p.2)
      Work.FTS.EllipticEst.Q0 from hG)

/-! ## The second `θ`-derivative of the angular source -/

/-- **The order-`2` `∂_θ`-expansion of the angular source.**  For `F` and `Ψ` of class `C^∞`
on the open quadrant and every interior point,

  `∂_θ²(Gsrc α F Ψ) = ∂_θ²F + α² ∂_θ²(z²∂_z²Ψ) + α(5+α) ∂_θ²(D_zΨ)`. -/
theorem GsrcPthTwo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
        = Work.Spaces.pthIter 2 F z θ
          + α ^ 2 * Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z θ hz hθ
  have hg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul _ (hΨ.pzIter 2)
  have hh : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have hmain := pthIter_three_lin hF hg hh (α ^ 2) (α * (5 + α)) 2 z θ hz hθ
  exact hmain

end Work.FTS.EllipticEst.SrcBnd
