import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.CoreResiduals.BiotSavart.continuousOn_farStrip_blocks
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- The spatial derivative of a time slice of a two-variable map, from its joint derivative at
`(x,t)`: the chain rule with the inclusion `y ↦ (y,t)` (whose Fréchet derivative is
`ContinuousLinearMap.inl ℝ R3 ℝ`). -/
private theorem fderiv_slice_eq_aux {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- **The first block of `fderiv ℝ (extField ω S)` on the strip.**  For a point `(x,t)` with
`t ∈ Icc 0 S` at which the spacetime field `extField ω S : R3 × ℝ → R3` (defined in
`Submission/Work/CoreResiduals/BiotSavart/continuousOn_farStrip_blocks.lean` as
`fun p => BS (windowExt ω S · p.2) p.1`) is `C¹`, the composition of its Fréchet derivative with
the spatial inclusion `ContinuousLinearMap.inl ℝ R3 ℝ` is the spatial derivative of the slice:
`fderiv ℝ (BS (ω(·,t))) x`.

Proof: `extField ω S = Function.uncurry (bsSTField (windowExt ω S))` (`extField_eq_uncurry`), so
`(fun x' => extField ω S (x',t)) = fun x' => BS (windowExt ω S · t) x'`; the chain rule with
`hasFDerivAt_prodMk_left` (and `ContDiffAt.differentiableAt`/`HasFDerivAt.comp`) gives
`(fderiv ℝ (extField ω S) (x,t)).comp (inl ℝ R3 ℝ)` as the derivative of that map at `x`; then
`windowExt_of_mem_Icc ht` gives `(fun y => windowExt ω S y t) = (fun y => ω y t)`, hence the same
Biot–Savart fields. -/
theorem fderiv_slice_ext_eq {ω : R3 → ℝ → R3} {S : ℝ} {x : R3} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x
      = (fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  have hdiff : DifferentiableAt ℝ (extField ω S) (x, t) := hcd.differentiableAt (by norm_num)
  have hwindow : (fun y => windowExt ω S y t) = (fun y => ω y t) :=
    funext fun y => windowExt_of_mem_Icc ht
  have hslice := fderiv_slice_eq_aux (u := bsSTField (windowExt ω S)) (x := x) (t := t) hdiff
  simp only [bsSTField, hwindow] at hslice
  exact hslice

end Work.CoreResiduals.BiotSavart
