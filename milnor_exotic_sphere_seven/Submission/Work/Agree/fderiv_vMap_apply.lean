import Mathlib
import Submission.Work.Milnor.VBundleDefs
import Submission.Work.Milnor.Clutch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Fréchet derivative of the clutching map `vMap (-2)`

`Submission.Milnor.vMap (-2)` is the gluing map of the two charts of the total space of the
rank-`4` bundle `ξ` over `S⁴` (Milnor's construction), `p ↦ (x/‖x‖², û² y û⁻¹)` with
`û = x/‖x‖`.  This file computes its Fréchet derivative in terms of the derivatives of its two
components.

The proof is a straight product-rule computation: `vMap (-2)` is a pair whose second component is
the product `(û²) * y * (û⁻¹)`, and the derivative of such a product in the total space
`ℝ⁴ × ℍ` splits, by the product rule, into the "base" contribution
(`fderiv` of `z ↦ û(z)² * y * û(z)⁻¹`) and the "fibre" contribution (`û² * · * û⁻¹`).
-/

namespace Work.Agree

open scoped Manifold ContDiff Topology RightActions
open TopologicalSpace Set
open Submission.Milnor

noncomputable section

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "HH" => Quaternion ℝ

/-! ### Differentiability of the direction maps -/

/-- The normalisation `x ↦ x/‖x‖` (as a quaternion valued map) is differentiable away from the
origin. -/
private lemma differentiableAt_dirVal (x : E4) (hx : x ≠ 0) :
    DifferentiableAt ℝ Work.Milnor.dirVal x :=
  ((contMDiffOn_iff_contDiffOn.mp Work.Milnor.dirVal_contMDiffOn).differentiableOn
      (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hx)

/-- The inversion `x ↦ x/‖x‖²` is differentiable away from the origin. -/
private lemma differentiableAt_invBase (x : E4) (hx : x ≠ 0) :
    DifferentiableAt ℝ invBase x :=
  ((contMDiffOn_iff_contDiffOn.mp contMDiffOn_invBase).differentiableOn
      (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hx)

/-- `x ↦ ((unitDir x : QS3) : ℍ)` is differentiable away from the origin (there it agrees with
`dirVal`). -/
private lemma differentiableAt_unitDir_coe (x : E4) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun z : E4 => ((unitDir z : QS3) : HH)) x := by
  have heq : (fun z : E4 => ((unitDir z : QS3) : HH)) =ᶠ[𝓝 x] Work.Milnor.dirVal := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    exact Work.Milnor.unitDir_coe z hz
  exact heq.differentiableAt_iff.mpr (differentiableAt_dirVal x hx)

/-! ### Chain rule for `p ↦ F p.1` -/

private lemma fderiv_comp_fst {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E4 → G) (x : MSpace8) (hF : DifferentiableAt ℝ F x.1) :
    fderiv ℝ (fun p : MSpace8 => F p.1) x
      = (fderiv ℝ F x.1).comp (ContinuousLinearMap.fst ℝ E4 HH) := by
  rw [show (fun p : MSpace8 => F p.1) = F ∘ Prod.fst from rfl,
    fderiv_comp x hF differentiableAt_fst, fderiv_fst]

private lemma fderiv_comp_fst_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E4 → G) (x v : MSpace8) (hF : DifferentiableAt ℝ F x.1) :
    fderiv ℝ (fun p : MSpace8 => F p.1) x v = fderiv ℝ F x.1 v.1 := by
  rw [fderiv_comp_fst F x hF]
  rfl

/-! ### Product rules -/

/-- Derivative in the total space of `p ↦ f p.1 * p.2 * g p.1`. -/
private lemma fderiv_mul_snd_mul (f g : E4 → HH) (x v : MSpace8)
    (hf : DifferentiableAt ℝ f x.1) (hg : DifferentiableAt ℝ g x.1) :
    fderiv ℝ (fun p : MSpace8 => f p.1 * p.2 * g p.1) x v
      = (f x.1 * x.2) * (fderiv ℝ g x.1 v.1)
        + (f x.1 * v.2 + (fderiv ℝ f x.1 v.1) * x.2) * g x.1 := by
  have h1 : HasFDerivAt (fun p : MSpace8 => f p.1)
      ((fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ E4 HH)) x :=
    hf.hasFDerivAt.comp x hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : MSpace8 => p.2) (ContinuousLinearMap.snd ℝ E4 HH) x :=
    hasFDerivAt_snd
  have h3 : HasFDerivAt (fun p : MSpace8 => g p.1)
      ((fderiv ℝ g x.1).comp (ContinuousLinearMap.fst ℝ E4 HH)) x :=
    hg.hasFDerivAt.comp x hasFDerivAt_fst
  have h4 : HasFDerivAt (fun p : MSpace8 => f p.1 * p.2)
      (f x.1 • ContinuousLinearMap.snd ℝ E4 HH
        + ((fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ E4 HH)) <• x.2) x := h1.mul' h2
  have h5 : HasFDerivAt (fun p : MSpace8 => f p.1 * p.2 * g p.1)
      ((f x.1 * x.2) • ((fderiv ℝ g x.1).comp (ContinuousLinearMap.fst ℝ E4 HH))
        + (f x.1 • ContinuousLinearMap.snd ℝ E4 HH
            + ((fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ E4 HH)) <• x.2) <• g x.1) x :=
    h4.mul' h3
  rw [h5.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

/-- Derivative in the base of `t ↦ f t * y * g t`. -/
private lemma fderiv_mul_const_mul (f g : E4 → HH) (z w : E4) (y : HH)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    (fderiv ℝ (fun t : E4 => f t * y * g t) z) w
      = (f z * y) * (fderiv ℝ g z w) + ((fderiv ℝ f z w) * y) * g z := by
  have ha : HasFDerivAt (fun t : E4 => f t * y) ((fderiv ℝ f z).smulRight y) z :=
    hf.hasFDerivAt.mul_const' y
  have hb : HasFDerivAt g (fderiv ℝ g z) z := hg.hasFDerivAt
  have h := ha.mul' hb
  rw [show (fun t : E4 => f t * y * g t) = (fun t : E4 => f t * y) * g from rfl, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]

/-! ### The main computation -/

theorem fderiv_vMap_apply (x : Submission.Milnor.MSpace8) (hx : x.1 ≠ 0)
    (v : Submission.Milnor.MSpace8) :
    fderiv ℝ (Submission.Milnor.vMap (-2)) x v
      = (fderiv ℝ Submission.Milnor.invBase x.1 v.1,
         (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) =>
            ((Submission.Milnor.unitDir z : Submission.Milnor.QS3) : Quaternion ℝ) ^ 2 * x.2 *
              (((Submission.Milnor.unitDir z : Submission.Milnor.QS3) : Quaternion ℝ))⁻¹) x.1) v.1
         + (((Submission.Milnor.unitDir x.1 : Submission.Milnor.QS3) : Quaternion ℝ)) ^ 2 * v.2 *
              (((Submission.Milnor.unitDir x.1 : Submission.Milnor.QS3) : Quaternion ℝ))⁻¹) := by
  have hu : DifferentiableAt ℝ (fun z : E4 => ((unitDir z : QS3) : HH)) x.1 :=
    differentiableAt_unitDir_coe x.1 hx
  have hu0 : ((unitDir x.1 : QS3) : HH) ≠ 0 := by
    have h1 : ‖((unitDir x.1 : QS3) : HH)‖ = 1 := norm_coe (unitDir x.1)
    exact norm_ne_zero_iff.mp (by rw [h1]; exact one_ne_zero)
  have hf : DifferentiableAt ℝ (fun z : E4 => ((unitDir z : QS3) : HH) ^ 2) x.1 :=
    hu.pow 2
  have hg : DifferentiableAt ℝ (fun z : E4 => (((unitDir z : QS3) : HH))⁻¹) x.1 :=
    hu.inv hu0
  have hF : DifferentiableAt ℝ invBase x.1 := differentiableAt_invBase x.1 hx
  -- identify `vMap (-2)` with its explicit two-component form
  rw [show vMap (-2) = (fun p : MSpace8 =>
        (invBase p.1,
          ((unitDir p.1 : QS3) : HH) ^ 2 * p.2 * (((unitDir p.1 : QS3) : HH))⁻¹)) from by
      funext p; simp only [vMap, vTwist]; norm_num]
  have hcomp1 : DifferentiableAt ℝ (fun p : MSpace8 => invBase p.1) x :=
    hF.comp x differentiableAt_fst
  have hcomp2 : DifferentiableAt ℝ (fun p : MSpace8 =>
      ((unitDir p.1 : QS3) : HH) ^ 2 * p.2 * (((unitDir p.1 : QS3) : HH))⁻¹) x := by
    have h1 : DifferentiableAt ℝ (fun p : MSpace8 => ((unitDir p.1 : QS3) : HH)) x :=
      hu.comp x differentiableAt_fst
    have h2 : DifferentiableAt ℝ (fun p : MSpace8 => ((unitDir p.1 : QS3) : HH) ^ 2) x :=
      h1.pow 2
    have h3 : DifferentiableAt ℝ (fun p : MSpace8 => (((unitDir p.1 : QS3) : HH))⁻¹) x :=
      h1.inv hu0
    exact (h2.mul differentiableAt_snd).mul h3
  rw [DifferentiableAt.fderiv_prodMk hcomp1 hcomp2, ContinuousLinearMap.prod_apply]
  refine Prod.ext ?_ ?_
  · rw [fderiv_comp_fst_apply invBase x v hF]
  · rw [fderiv_mul_snd_mul (f := fun z : E4 => ((unitDir z : QS3) : HH) ^ 2)
        (g := fun z : E4 => (((unitDir z : QS3) : HH))⁻¹) x v hf hg,
      fderiv_mul_const_mul (f := fun z : E4 => ((unitDir z : QS3) : HH) ^ 2)
        (g := fun z : E4 => (((unitDir z : QS3) : HH))⁻¹) x.1 v.1 x.2 hf hg]
    noncomm_ring

end

end Work.Agree
