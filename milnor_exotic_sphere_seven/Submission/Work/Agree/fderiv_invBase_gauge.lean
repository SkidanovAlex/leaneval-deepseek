import Mathlib
import Submission.Work.Agree.gaugeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The derivative of the inversion `x ↦ x/‖x‖²`, in quaternionic form

`Submission.Milnor.invBase x = x / ‖x‖²` is the inversion of `ℝ⁴` used in the definition of the
gluing map `vMap (-2)` of the rank-`4` bundle `ξ` over `S⁴ = OnePoint ℝ⁴`.  This file computes its
Fréchet derivative at `x ≠ 0` in the quaternionic form needed by the gauge construction
(see `GEOMETRYB_PLAN.md`, item L1 + L3):

    fderiv ℝ invBase x = -‖x‖⁻² • (qTwist 1 1 u ∘ gaugeJ),   u = unitDir x ∈ S³ ⊆ ℍ,

where `gaugeJ` is the real-linear map of the standard fibre `ℝ⁴` induced by quaternion conjugation
and `qTwist 1 1 u` is `v ↦ u * v * u`.

The computation has two halves:

* the calculus (`fderiv ℝ (x ↦ ‖x‖⁻² • x)`): the derivative is
  `‖x‖⁻² • 1 - (2‖x‖⁻⁴) • (⟪x,·⟫ • x)`, the classical reflection `v ↦ ‖x‖⁻² (v - 2⟪u,v⟫u)` with
  `u = x/‖x‖`;
* the quaternion identity `-(u * star w * u) = w - 2⟪u,w⟫ • u` for `u` of norm one, which rewrites
  the reflection as the map `v ↦ -‖x‖⁻² • (u * star v * u)` — here `star` is conjugation in `ℍ`.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set

namespace Work.Agree

noncomputable section

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "HH" => Quaternion ℝ

/-! ## The quaternionic reflection identity -/

/-- For any two quaternions, `star u * w + star w * u` is the real number `2⟪u,w⟫`.  (This is just
the statement that `w ↦ star u * w` is the adjoint of `w ↦ star w * u`; no hypothesis on `u`.) -/
lemma star_mul_add_star_mul (u w : HH) :
    star u * w + star w * u = ((2 : ℝ) * ⟪u, w⟫) • (1 : HH) := by
  have hsa : star (star u * w + star w * u) = star u * w + star w * u := by
    simp [star_add, star_mul, add_comm]
  have h2 : star u * w + star w * u = ((star u * w + star w * u).re : ℝ) :=
    Quaternion.star_eq_self.mp hsa
  rw [h2, Quaternion.inner_def, Algebra.smul_def, Quaternion.algebraMap_def, mul_one]
  congr 1
  simp only [Quaternion.re_add, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **The quaternionic form of the reflection.**  For a unit quaternion `u` (written here as
`u * star u = 1`), the reflection in the hyperplane orthogonal to `u`,
`w ↦ w - 2⟪u,w⟫ u`, is `w ↦ -(u * star w * u)`. -/
lemma neg_mul_star_mul (u w : HH) (hu : u * star u = 1) :
    -(u * star w * u) = w - ((2 : ℝ) * ⟪u, w⟫) • u := by
  have h1 := congrArg (fun z : HH => u * z) (star_mul_add_star_mul u w)
  simp only [mul_add, mul_smul_comm, mul_one, ← mul_assoc] at h1
  rw [hu, one_mul] at h1
  have h2 : u * star w * u = ((2 : ℝ) * ⟪u, w⟫) • u - w := by
    rw [eq_sub_iff_add_eq, add_comm]; exact h1
  rw [h2]
  abel

/-! ## The derivative of the inversion -/

/-- The Fréchet derivative of `invBase` at `x ≠ 0`, in the "vector calculus" form. -/
lemma fderiv_invBase_eq (x : E4) (hx : x ≠ 0) :
    fderiv ℝ Submission.Milnor.invBase x
      = (‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E4
        + (-((‖x‖ ^ 2) ^ 2)⁻¹ • (2 • innerSL ℝ x)).smulRight x := by
  have hc : HasFDerivAt (fun y : E4 => (‖y‖ ^ 2)⁻¹)
      (-((‖x‖ ^ 2) ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    have hg : HasFDerivAt (fun y : E4 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hz : (‖x‖ ^ 2) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    have hd : HasDerivAt (fun z : ℝ => z⁻¹) (-((‖x‖ ^ 2) ^ 2)⁻¹) (‖x‖ ^ 2) := by
      simpa using hasDerivAt_inv hz
    exact hd.comp_hasFDerivAt x hg
  rw [show Submission.Milnor.invBase = (fun y : E4 => (‖y‖ ^ 2)⁻¹ • id y) from rfl]
  rw [fderiv_fun_smul hc.differentiableAt differentiableAt_id, fderiv_id, hc.fderiv]
  simp

/-- **The derivative of the inversion, in quaternionic form**: with `u = unitDir x ∈ S³ ⊆ ℍ` the
unit quaternion in the direction of `x`,

    `fderiv ℝ invBase x = -‖x‖⁻² • (qTwist 1 1 u ∘ gaugeJ)`,

i.e. the tangent map of `x ↦ x/‖x‖²` at `x` is `v ↦ -‖x‖⁻² u v̄ u`. -/
theorem fderiv_invBase_gauge (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) :
    fderiv ℝ Submission.Milnor.invBase x
      = -((‖x‖ ^ 2)⁻¹) • ((Work.Agree.qTwist (1 : ℤ) 1
          (((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : Quaternion ℝ))).comp
            Work.Agree.gaugeJ) := by
  have hL := fderiv_invBase_eq x hx
  set k : ℝ := ‖x‖ with hk_def
  have hk : k ≠ 0 := by rw [hk_def]; exact norm_ne_zero_iff.mpr hx
  set u : HH := ((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : HH) with hu_def
  have hu : u * star u = 1 := by
    rw [hu_def]
    have h1 : ‖(((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : HH))‖ = 1 :=
      Work.Milnor.norm_unitDir_coe x
    rw [Quaternion.mul_star_eq_coe, ← Quaternion.normSq_def, Quaternion.normSq_eq_norm_mul_self,
      h1, mul_one, Quaternion.coe_one]
  -- `toQ x = k • u`, i.e. `x = k • ofQ u`
  have htoQx : toQ x = k • u := by
    have h1 : u = (k : ℝ)⁻¹ • toQ x := by
      rw [hu_def, hk_def, Work.Milnor.unitDir_coe x hx, Work.Milnor.dirVal]; rfl
    rw [h1, smul_smul, mul_inv_cancel₀ hk, one_smul]
  have hx_eq : x = k • ofQ u := by
    conv_lhs => rw [← ofQ_toQ x]
    rw [htoQx, map_smul]
  -- the inner products are related by the factor `k`
  have hinner : ∀ v : E4, ⟪x, v⟫ = k * ⟪u, toQ v⟫ := by
    intro v
    have hiso : ⟪toQ x, toQ v⟫ = ⟪x, v⟫ :=
      LinearIsometryEquiv.inner_map_map Quaternion.linearIsometryEquivTuple.symm x v
    rw [← hiso, htoQx, real_inner_smul_left]
  rw [hL]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, qTwist_apply, gaugeJ_apply,
    toQ_ofQ, zpow_one]
  rw [innerSL_apply_apply, hinner v, hx_eq, ← ofQ_toQ v]
  simp only [toQ_ofQ]
  rw [smul_smul]
  -- the scalar bookkeeping
  have hscal : -((k ^ 2) ^ 2)⁻¹ • 2 • (k * ⟪u, toQ v⟫) * k
      = -(k ^ 2)⁻¹ * (2 * ⟪u, toQ v⟫) := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hscal]
  rw [neg_smul, ← smul_neg, ← map_neg, neg_mul_star_mul u (toQ v) hu, map_sub, map_smul,
    smul_sub, smul_smul]
  rw [neg_mul, neg_smul, sub_eq_add_neg]

end

end Work.Agree
