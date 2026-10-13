import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The divergence of the stream-function field `psiField ψ`

Off the axis, the no-swirl axisymmetric field with stream function `ψ`,
`u_r = ∂_z ψ`, `u_z = -(ψ/r) - ∂_r ψ`, is divergence free.  Indeed, in the cylindrical
coordinates of `Work.Cyl`, `div u = ∂_r u_r + u_r/r + ∂_z u_z`, and with the above `u_r, u_z`

`∂_r u_r + u_r / r + ∂_z u_z = ∂_r ∂_z ψ + (∂_z ψ)/r - (∂_z ψ)/r - ∂_z ∂_r ψ = 0`

by the symmetry of the mixed second partials of `ψ`.

This file proves that statement (`Work.Cyl.div_psiField`).  Along the way it builds the small
amount of second-derivative API for the *curried* partials `pdR`, `pdZ` that the argument needs:
the pair map `(r,z) ↦ pdR ψ r z` (resp. `(r,z) ↦ pdZ ψ r z`) of a `C²` function is differentiable
(its value being `fderiv` of the uncurried function evaluated on `(1,0)`, resp. `(0,1)`), and the
two mixed second partials agree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-! ## Differentiating the evaluation of a continuous linear map -/

private lemma fderiv_eval_const (G : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (v p₀ : ℝ × ℝ)
    (hG : DifferentiableAt ℝ G p₀) :
    fderiv ℝ (fun p => G p v) p₀ = (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ G p₀) := by
  have hL : HasFDerivAt (fun y : (ℝ × ℝ) →L[ℝ] ℝ => y v)
      ((ContinuousLinearMap.apply ℝ ℝ v) : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ) (G p₀) := by
    have h0 := ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ v : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ) (x := G p₀)
    rw [show (⇑(ContinuousLinearMap.apply ℝ ℝ v : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ)) = (fun y => y v)
      from by funext y; exact ContinuousLinearMap.apply_apply v y] at h0
    exact h0
  have hcomp := hL.comp p₀ hG.hasFDerivAt
  rw [show (fun p => G p v) = ((fun y : (ℝ × ℝ) →L[ℝ] ℝ => y v) ∘ G) from rfl] at *
  exact hcomp.fderiv

/-! ## The pair maps of `pdR f` and `pdZ f` for a `C²` function -/

/-- If `(r,z) ↦ ψ r z` is `C²` near `(r,z)`, then `(r,z) ↦ ∂_r ψ (r,z)` is differentiable there:
it is the `fderiv` of the uncurried function, evaluated on `(1,0)`. -/
private theorem diffAt2_pdR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : DiffAt2 (pdR f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => pdR f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_fst f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((1, 0) : ℝ × ℝ))

/-- If `(r,z) ↦ ψ r z` is `C²` near `(r,z)`, then `(r,z) ↦ ∂_z ψ (r,z)` is differentiable there:
it is the `fderiv` of the uncurried function, evaluated on `(0,1)`. -/
private theorem diffAt2_pdZ_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : DiffAt2 (pdZ f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => pdZ f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_snd f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((0, 1) : ℝ × ℝ))

/-! ## Symmetry of the mixed second partials -/

/-- For a `C²` function of two variables, the two mixed second partials of the curried function
agree (`Clairaut`), the common value being the (symmetric) second `fderiv` of the uncurried
function evaluated on the two coordinate directions. -/
private theorem pdRZ_eq_pdZR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : pdRZ f r z = pdZR f r z := by
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have hdR : DiffAt2 (pdR f) r z := diffAt2_pdR_of_contDiffAt_two f r z h
  have hdZ : DiffAt2 (pdZ f) r z := diffAt2_pdZ_of_contDiffAt_two f r z h
  have hZev : (fun p : ℝ × ℝ => pdZ f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_snd f p.1 p.2 hp).symm
  have hRev : (fun p : ℝ × ℝ => pdR f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_fst f p.1 p.2 hp).symm
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  have hsymm : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) :=
    h.isSymmSndFDerivAt (by simp)
  have e1 : pdRZ f r z = fderiv ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z) (1, 0) := by
    rw [show pdRZ f r z = pdR (pdZ f) r z from rfl,
      ← fderiv_prod_apply_fst (pdZ f) r z hdZ]
  have e4 : fderiv ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z) (0, 1) = pdZR f r z := by
    rw [fderiv_prod_apply_snd (pdR f) r z hdR]
    rfl
  calc pdRZ f r z
      = fderiv ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z) (1, 0) := e1
    _ = fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1))
          (r, z) (1, 0) := by
        rw [Filter.EventuallyEq.fderiv_eq hZev]
    _ = (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) (1, 0)) (0, 1) := by
        rw [fderiv_eval_const _ (0, 1) (r, z) hG, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply]
    _ = (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) (0, 1)) (1, 0) :=
        hsymm.eq (1, 0) (0, 1)
    _ = fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0))
          (r, z) (0, 1) := by
        rw [fderiv_eval_const _ (1, 0) (r, z) hG, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply]
    _ = fderiv ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z) (0, 1) := by
        rw [Filter.EventuallyEq.fderiv_eq hRev]
    _ = pdZR f r z := e4

/-! ## The two-variable field `u_z = -(ψ/r) - ∂_r ψ` -/

/-- The partial derivative in `z` of `u_z(r,z) = -(ψ r z)/r - ∂_r ψ (r,z)`. -/
private theorem pdZ_uz_eq (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : DiffAt2 ψ r z) (hdR : DiffAt2 (pdR ψ) r z) :
    pdZ (fun r z => -(ψ r z / r) - pdR ψ r z) r z = -(pdZ ψ r z) / r - pdZR ψ r z := by
  have hA : HasDerivAt (fun z' : ℝ => ψ r z' / r) (pdZ ψ r z / r) z :=
    (differentiableAt_slice_snd ψ r z hψ).hasDerivAt.div_const r
  have hB : HasDerivAt (fun z' : ℝ => pdR ψ r z') (pdZR ψ r z) z := by
    have h : DifferentiableAt ℝ (fun z' : ℝ => pdR ψ r z') z :=
      hdR.comp z ((differentiableAt_const r).prodMk (differentiableAt_id (x := z)))
    exact h.hasDerivAt
  have hsum : HasDerivAt (fun z' : ℝ => -(ψ r z' / r) - pdR ψ r z')
      (-(pdZ ψ r z / r) - pdZR ψ r z) z := hA.neg.sub hB
  rw [pdZ, hsum.deriv, neg_div]

/-- Differentiability of the two-variable function `u_z(r,z) = -(ψ r z)/r - ∂_r ψ (r,z)` off the
axis. -/
private theorem diffAt2_uz (ψ : ℝ → ℝ → ℝ) (r z : ℝ) (hr : r ≠ 0)
    (hψ : DiffAt2 ψ r z) (hdR : DiffAt2 (pdR ψ) r z) :
    DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - pdR ψ p.1 p.2) (r, z)
  have hψ' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z) := hψ
  have hdiv : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2 / p.1) (r, z) := by
    fun_prop (disch := exact hr)
  have hdR' : DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (r, z) := hdR
  exact hdiv.neg.sub hdR'

/-! ## The main theorem -/

theorem div_psiField (ψ : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (Work.Cyl.psiField ψ) x = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hdψ : DiffAt2 ψ (radial x) (axial x) := hψ.differentiableAt (by simp)
  have hdR : DiffAt2 (pdR ψ) (radial x) (axial x) := diffAt2_pdR_of_contDiffAt_two ψ _ _ hψ
  have hdZ : DiffAt2 (pdZ ψ) (radial x) (axial x) := diffAt2_pdZ_of_contDiffAt_two ψ _ _ hψ
  have huz : DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) (radial x) (axial x) :=
    diffAt2_uz ψ _ _ hrne hdψ hdR
  have hval := pdZ_uz_eq ψ (radial x) (axial x) hdψ hdR
  have hcl := pdRZ_eq_pdZR_of_contDiffAt_two ψ (radial x) (axial x) hψ
  show FiniteTimeSingularity.div
    (cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z)) x = 0
  rw [div_cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) x hdZ huz hr]
  rw [show pdR (pdZ ψ) (radial x) (axial x) = pdRZ ψ (radial x) (axial x) from rfl, hval, hcl]
  ring

end Work.Cyl
