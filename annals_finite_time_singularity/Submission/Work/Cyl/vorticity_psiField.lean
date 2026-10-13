import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.vortTheta_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of the stream-function field `psiField ψ`

If `ψ` is a `C²` stream function then the vorticity of the axisymmetric no-swirl field
`psiField ψ = u_r e_r + u_z e_θ` (paper (PsiTou)) has only the angular component, equal to
`ω^θ = -Lψ` where `L = cylOp` is the axisymmetric elliptic operator of (3dBSL):

  `∇ × (psiField ψ) x = -cylOp ψ (radial x) (axial x) • eTheta x`.

This combines the coordinate description of the curl of `cylField` (`vorticity_cylField`)
with the stream-function identity `vortTheta_psiField`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix Topology
open Work.Cyl

namespace Work.Cyl

/-- If `ψ : ℝ × ℝ → ℝ` is `C²` at `(r,z)`, then its radial partial derivative
`p ↦ pdR ψ p.1 p.2` is differentiable at `(r,z)`.

Indeed, `pdR ψ p.1 p.2 = fderiv ℝ (uncurry ψ) p (1,0)` at every point `p` where `ψ` is
differentiable, and `fderiv ℝ (uncurry ψ)` is `C¹` (hence differentiable) at `(r,z)` because
`uncurry ψ` is `C²` there. -/
lemma differentiableAt_pdR (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`.
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ (uncurry ψ)` is `C¹`, hence differentiable, at `(r,z)`.
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hfd.differentiableAt_one
  -- evaluating the derivative at the fixed direction `(1,0)` preserves differentiability.
  have hΦ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).differentiableAt).comp (r, z) hfdd
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-- If `ψ : ℝ × ℝ → ℝ` is `C²` at `(r,z)`, then its axial partial derivative
`p ↦ pdZ ψ p.1 p.2` is differentiable at `(r,z)`. -/
lemma differentiableAt_pdZ (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => pdZ ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hfd.differentiableAt_one
  have hΦ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).differentiableAt).comp (r, z) hfdd
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The vorticity of the stream-function field `psiField ψ` off the axis is `-cylOp ψ` times the
angular vector `e_θ`. -/
theorem vorticity_psiField (ψ : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.vorticity (Work.Cyl.psiField ψ) x =
      -Work.Cyl.cylOp ψ (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := by
  have hR : radial x ≠ 0 := ne_of_gt hr
  have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (radial x, axial x) :=
    hψ.differentiableAt (by norm_num)
  have hpdR : DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (radial x, axial x) :=
    differentiableAt_pdR ψ (radial x) (axial x) hψ
  -- the two components of `psiField ψ` are differentiable at `(radial x, axial x)`
  have hur : DiffAt2 (pdZ ψ) (radial x) (axial x) :=
    differentiableAt_pdZ ψ (radial x) (axial x) hψ
  have huz : DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) (radial x) (axial x) := by
    show DifferentiableAt ℝ
      (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - pdR ψ p.1 p.2) (radial x, axial x)
    fun_prop
  -- the coordinate form of the curl, and the stream-function identity
  have hcurl := vorticity_cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) x hur huz hr
  have hvt := vortTheta_psiField ψ (radial x) (axial x) hψ hR
  rw [show psiField ψ = cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) from rfl]
  rw [hcurl, hvt]

end Work.Cyl
