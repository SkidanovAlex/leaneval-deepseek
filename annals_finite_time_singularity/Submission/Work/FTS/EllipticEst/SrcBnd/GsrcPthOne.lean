import Mathlib.Analysis.Calculus.ContDiff.Defs
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

namespace Work.FTS.EllipticEst.SrcBnd

theorem GsrcPthOne {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pthIter 1 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
        = Work.Spaces.pthIter 1 F z θ
          + α ^ 2 * Work.Spaces.pthIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + α * (5 + α) * Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z θ hz hθ
  -- `pthIter 1 = pth`, `pth f z θ = deriv (fun θ' => f z θ') θ`, and `Gsrc` is the pointwise sum
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
    Work.FTS.EllipticEst.Mine.Gsrc, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz]
  -- the two inner slices (with the `z`-dependent constants pulled out of the derivative)
  have h2diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ :=
    ((hΨ.pzIter 2).curry_θ hz).differentiableOn (by simp) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have h3diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz Ψ z θ') θ :=
    ((hΨ.pz).curry_θ hz).differentiableOn (by simp) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hA : deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = z ^ 2 * deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ :=
    deriv_const_mul (z ^ 2) h2diff
  have hB : deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ := deriv_const_mul z h3diff
  rw [hA, hB]
  -- differentiate the pointwise sum of the three slices
  have hFd : HasDerivAt (fun θ' => F z θ') (deriv (fun θ' => F z θ') θ) θ :=
    ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hA0d : HasDerivAt (fun θ' => Work.Spaces.pzIter 2 Ψ z θ')
      (deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ) θ := h2diff.hasDerivAt
  have hB0d : HasDerivAt (fun θ' => Work.Spaces.pz Ψ z θ')
      (deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ) θ := h3diff.hasDerivAt
  have h := ((hFd.add ((hA0d.const_mul (z ^ 2)).const_mul (α ^ 2))).add
    ((hB0d.const_mul z).const_mul (α * (5 + α))))
  exact h.deriv

end Work.FTS.EllipticEst.SrcBnd
