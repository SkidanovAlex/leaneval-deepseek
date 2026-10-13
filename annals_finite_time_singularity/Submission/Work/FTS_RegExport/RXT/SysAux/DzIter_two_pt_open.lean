import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two-point expansion `D_z² = D_z + z²∂_z²` with only an open, `C²` hypothesis

`Work.Spaces.DzIter_two_pt` proves the expansion `D_z² h = z ∂_z h + z² ∂_z² h` under the
hypothesis that the `z`-slices are *analytic* (`ContDiffOn ℝ ⊤ ...`), which is far stronger than
what the consumers of this file have available: their slices are only `C²` on the open half-line
`(0,∞)`, and only for `θ` in the open interval `(0,π/2)`.

The proof here uses only that hypothesis.  Unfold `D_z² h = D_z (D_z h)` and
`D_z g z θ = z ∂_z g(z,θ)`: the identity is the one-variable product rule in `z` applied to
`t ↦ t · ∂_z h(t,θ)`, whose second factor is differentiable at `z` because a function that is `C²`
on the open set `(0,∞)` has a `C¹` derivative there
(`ContDiffOn.deriv_of_isOpen`, then `ContDiffOn.differentiableOn`).  The value of that derivative
is `∂_z²h(z,θ) = pzIter 2 h z θ` by definition of `pzIter`.
-/

open Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- **The expansion `D_z² = z ∂_z + z² ∂_z²` at a point, from `C²`-smoothness of the `z`-slices.**
For `z > 0` and `θ ∈ (0,π/2)`, if the `z`-slice `z' ↦ h z' θ` is `C²` on the open half-line
`(0,∞)`, then `D_z² h z θ = z ∂_z h z θ + z² ∂_z² h z θ`. -/
theorem DzIter_two_pt_open {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffOn ℝ 2 (fun z => h z θ) (Set.Ioi 0))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 h z θ = z * Work.Spaces.pzIter 1 h z θ
      + z ^ 2 * Work.Spaces.pzIter 2 h z θ := by
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
  -- the `z`-slice is `C²` on the open set `(0,∞)`, hence its derivative is `C¹` there
  have hcd : ContDiffOn ℝ 2 (fun z' : ℝ => h z' θ) (Set.Ioi 0) := hsmooth θ hθ
  have hd1 : ContDiffOn ℝ 1 (deriv (fun z' : ℝ => h z' θ)) (Set.Ioi 0) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by norm_num)
  -- so `t ↦ ∂_z h(t,θ) = pzIter 1 h t θ` is differentiable at `z`
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pzIter 1 h t θ) z := by
    have h2 : DifferentiableAt ℝ (deriv (fun z' : ℝ => h z' θ)) z :=
      (hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hzI)
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using h2
  have hdg : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz h t θ) z := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using hdiff
  -- the one-variable product rule for `t ↦ t * ∂_z h(t,θ)`
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz h t θ) z
      = Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ := by
    have h1' : deriv ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz h t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz h z θ
          + z * deriv (fun t : ℝ => Work.Spaces.pz h t θ) z :=
      deriv_mul (c := fun t : ℝ => t) (d := fun t : ℝ => Work.Spaces.pz h t θ)
        differentiableAt_id hdg
    rw [show (fun t : ℝ => t * Work.Spaces.pz h t θ)
          = ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz h t θ) from rfl,
        h1', deriv_id'', one_mul]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  -- and the definitional unfolding `D_z² h z θ = z * ∂_z (t ↦ t * ∂_z h(t,θ)) z`
  rw [show Work.Spaces.DzIter 2 h z θ
        = z * deriv (fun t : ℝ => t * Work.Spaces.pz h t θ) z from rfl, hderiv]
  show z * (Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ)
      = z * Work.Spaces.pzIter 1 h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ
  rw [show Work.Spaces.pzIter 1 h = Work.Spaces.pz h from rfl]
  ring

end Work.FTS_RegExport.RXT.SysAux
