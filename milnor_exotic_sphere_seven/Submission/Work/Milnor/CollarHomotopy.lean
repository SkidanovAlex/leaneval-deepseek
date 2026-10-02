import Mathlib
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Milnor.UnitSphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The collar `{1/2 < ν}` of the disc bundle is homotopy equivalent to the sphere bundle `Mk k`

The collar `collar k = {p : Vk k | 1/2 < fibreNormFun k p}` is an open neighbourhood of the unit
sphere bundle of `ξ`.  Because `fibreNormFun k > 1/2 > 0` on the collar, the fibrewise scaling
`vScale` (`Submission.Work.Milnor.ScaleDefs`) normalises every point of the collar to the unit
sphere bundle, giving a continuous retraction

`collarNorm k : ↥(collar k) → {p : Vk k // fibreNormFun k p = 1}`,
`collarNorm k p = ⟨(fibreNormFun k p)⁻¹ • p, _⟩`

of the collar onto the unit sphere bundle, and the straight-line homotopy
`(t, p) ↦ ((1-t) · (fibreNormFun k p)⁻¹ + t) • p` deforms the identity of the collar to
`collarPhi ∘ collarPsi`.  Composing `collarNorm k` with the inverse `unitInv k` of the inclusion
`mkToVkFun k : Mk k → Vk k` (`Submission.Work.Milnor.UnitSphere`) turns this into a homotopy
equivalence between the collar and `Mk k`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor
open Set

noncomputable section

/-! ## An elementary convexity estimate -/

/-- A convex combination of `1` and a number `> 1/2` is `> 1/2`. -/
theorem half_lt_affine (t w : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hw : 1 / 2 < w) :
    1 / 2 < 1 - t + t * w := by
  by_cases hw1 : w ≤ 1
  · nlinarith [mul_le_mul_of_nonneg_right ht1 (by linarith : (0 : ℝ) ≤ 1 - w), hw]
  · nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ w by linarith) ht0]

/-! ## The inclusion of `Mk k` in the collar -/

/-- The fibre norm of a point of the unit sphere bundle of `Mk k` is `1`. -/
theorem fibreNormFun_mkToVkFun (k : ℤ) (z : Mk k) : fibreNormFun k (mkToVkFun k z) = 1 :=
  (mem_range_mkToVkFun_iff k (mkToVkFun k z)).mp ⟨z, rfl⟩

theorem one_lt_fibreNorm_mkToVkFun (k : ℤ) (z : Mk k) :
    1 / 2 < fibreNormFun k (mkToVkFun k z) := by
  rw [fibreNormFun_mkToVkFun]
  norm_num

/-- **The inclusion of the sphere bundle `Mk k` in the collar**, as a continuous map. -/
noncomputable def collarPhi (k : ℤ) : C(Mk k, ↥(collar k)) :=
  ContinuousMap.mk (fun z => ⟨mkToVkFun k z, one_lt_fibreNorm_mkToVkFun k z⟩)
    (Continuous.subtype_mk (continuous_mkToVkFun k) (one_lt_fibreNorm_mkToVkFun k))

@[simp] theorem collarPhi_coe (k : ℤ) (z : Mk k) :
    ((collarPhi k z : ↥(collar k)) : Vk k) = mkToVkFun k z := rfl

/-! ## The normalisation of the collar onto the unit sphere bundle -/

theorem continuous_inv_fibreNorm_collar (k : ℤ) :
    Continuous (fun p : ↥(collar k) => (fibreNormFun k (p : Vk k))⁻¹) :=
  (((continuous_fibreNormFun k).comp continuous_subtype_val).inv₀ (fun p => by
    have hp := mem_collar.mp p.2
    simp only [Function.comp_apply]
    linarith))

/-- The normalisation map `p ↦ (ν p)⁻¹ • p` on the collar is continuous. -/
theorem continuous_vScale_inv_fibreNorm (k : ℤ) :
    Continuous (fun p : ↥(collar k) => vScale k ((fibreNormFun k (p : Vk k))⁻¹) (p : Vk k)) :=
  (continuous_vScale_uncurry k).comp
    (Continuous.prodMk (continuous_inv_fibreNorm_collar k) continuous_subtype_val)

/-- The normalised point lies on the unit sphere bundle: `ν ((ν p)⁻¹ • p) = 1`. -/
theorem fibreNormFun_vScale_inv (k : ℤ) (p : ↥(collar k)) :
    fibreNormFun k (vScale k ((fibreNormFun k (p : Vk k))⁻¹) (p : Vk k)) = 1 := by
  rw [fibreNormFun_vScale]
  have hpos : 0 < fibreNormFun k (p : Vk k) := by
    have hp := mem_collar.mp p.2
    linarith
  rw [abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]

/-- **The normalisation of the collar**: scaling each point by the inverse of its fibre norm,
which lands on the unit sphere bundle `{ν = 1}`. -/
noncomputable def collarNorm (k : ℤ) : C(↥(collar k), {p : Vk k // fibreNormFun k p = 1}) :=
  ContinuousMap.mk
    (fun p => ⟨vScale k ((fibreNormFun k (p : Vk k))⁻¹) (p : Vk k),
      fibreNormFun_vScale_inv k p⟩)
    (Continuous.subtype_mk (continuous_vScale_inv_fibreNorm k) (fibreNormFun_vScale_inv k))

@[simp] theorem collarNorm_coe (k : ℤ) (p : ↥(collar k)) :
    ((collarNorm k p : {p : Vk k // fibreNormFun k p = 1}) : Vk k)
      = vScale k ((fibreNormFun k (p : Vk k))⁻¹) (p : Vk k) := rfl

/-- **The retraction of the collar onto `Mk k`**: normalise the fibre coordinate and read off the
corresponding point of the sphere bundle `Mk k`. -/
noncomputable def collarPsi (k : ℤ) : C(↥(collar k), Mk k) :=
  (ContinuousMap.mk (unitInv k) (continuous_unitInv k)).comp (collarNorm k)

theorem collarPsi_apply (k : ℤ) (p : ↥(collar k)) :
    collarPsi k p = unitInv k (collarNorm k p) := rfl

/-! ## The two composites -/

theorem collarPsi_collarPhi (k : ℤ) :
    (collarPsi k).comp (collarPhi k) = ContinuousMap.id (Mk k) := by
  ext z
  have hnu : fibreNormFun k ((collarPhi k z : ↥(collar k)) : Vk k) = 1 :=
    fibreNormFun_mkToVkFun k z
  have h1 : ((collarNorm k (collarPhi k z) : {p : Vk k // fibreNormFun k p = 1}) : Vk k)
      = mkToVkFun k z := by
    rw [collarNorm_coe, hnu, inv_one, vScale_one]
    rfl
  have h2 : collarNorm k (collarPhi k z)
      = ⟨mkToVkFun k z, fibreNormFun_mkToVkFun k z⟩ := Subtype.ext h1
  show unitInv k (collarNorm k (collarPhi k z)) = z
  rw [h2]
  exact mkToVkFun_injective k (by rw [mkToVkFun_unitInv])

/-! ## The homotopy deforming the identity of the collar onto the normalisation -/

/-- The parameter of the straight-line deformation of the collar: from `(ν p)⁻¹` (the
normalisation) to `1` (the identity). -/
def collarParam (k : ℤ) (z : unitInterval × ↥(collar k)) : ℝ :=
  (1 - ((z.1 : unitInterval) : ℝ)) * (fibreNormFun k (z.2 : Vk k))⁻¹
    + ((z.1 : unitInterval) : ℝ)

theorem continuous_collarParam (k : ℤ) : Continuous (collarParam k) := by
  have h1 : Continuous (fun z : unitInterval × ↥(collar k) => ((z.1 : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun z : unitInterval × ↥(collar k) => (fibreNormFun k (z.2 : Vk k))⁻¹) :=
    (continuous_inv_fibreNorm_collar k).comp continuous_snd
  exact ((continuous_const.sub h1).mul h2).add h1

theorem collarParam_mem (k : ℤ) (z : unitInterval × ↥(collar k)) :
    vScale k (collarParam k z) (z.2 : Vk k) ∈ collar k := by
  rw [mem_collar, fibreNormFun_vScale]
  have ht0 : 0 ≤ ((z.1 : unitInterval) : ℝ) := z.1.2.1
  have ht1 : ((z.1 : unitInterval) : ℝ) ≤ 1 := z.1.2.2
  have hw : 1 / 2 < fibreNormFun k (z.2 : Vk k) := mem_collar.mp z.2.2
  have hpos : 0 < fibreNormFun k (z.2 : Vk k) := by linarith
  have hcnn : 0 ≤ collarParam k z := by
    have h1 : 0 ≤ 1 - ((z.1 : unitInterval) : ℝ) := by linarith
    have h2 : 0 ≤ (fibreNormFun k (z.2 : Vk k))⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
    have h3 : 0 ≤ (1 - ((z.1 : unitInterval) : ℝ)) * (fibreNormFun k (z.2 : Vk k))⁻¹ :=
      mul_nonneg h1 h2
    simp only [collarParam]
    linarith
  rw [abs_of_nonneg hcnn]
  have hmul : collarParam k z * fibreNormFun k (z.2 : Vk k)
      = 1 - ((z.1 : unitInterval) : ℝ) + ((z.1 : unitInterval) : ℝ)
        * fibreNormFun k (z.2 : Vk k) := by
    simp only [collarParam]
    rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
  rw [hmul]
  exact half_lt_affine _ _ ht0 ht1 hw

/-- **The straight-line homotopy** deforming the identity of the collar onto
`collarPhi k ∘ collarPsi k`. -/
noncomputable def collarHomotopy (k : ℤ) :
    ContinuousMap.Homotopy ((collarPhi k).comp (collarPsi k))
      (ContinuousMap.id (↥(collar k))) :=
  ContinuousMap.Homotopy.mk
    (ContinuousMap.mk
      (fun z : unitInterval × ↥(collar k) =>
        ⟨vScale k (collarParam k z) (z.2 : Vk k), collarParam_mem k z⟩)
      (Continuous.subtype_mk
        ((continuous_vScale_uncurry k).comp
          (Continuous.prodMk (continuous_collarParam k)
            (continuous_subtype_val.comp continuous_snd)))
        (collarParam_mem k)))
    (by
      intro p
      refine Subtype.ext ?_
      show vScale k (collarParam k (0, p)) (p : Vk k) = mkToVkFun k (collarPsi k p)
      have h0 : collarParam k (0, p) = (fibreNormFun k (p : Vk k))⁻¹ := by
        simp [collarParam]
      rw [h0, collarPsi_apply, mkToVkFun_unitInv]
      rfl)
    (by
      intro p
      refine Subtype.ext ?_
      show vScale k (collarParam k (1, p)) (p : Vk k) = (p : Vk k)
      have h1 : collarParam k (1, p) = 1 := by
        simp [collarParam]
      rw [h1, vScale_one]
      rfl)

/-! ## The homotopy equivalence -/

/-- **The collar of the disc bundle is homotopy equivalent to the sphere bundle `Mk k`.** -/
theorem collar_homotopyEquiv_aux (k : ℤ) :
    Nonempty (ContinuousMap.HomotopyEquiv (↥(collar k)) (Mk k)) :=
  ⟨ContinuousMap.HomotopyEquiv.mk (collarPsi k) (collarPhi k)
    ⟨collarHomotopy k⟩
    (by rw [collarPsi_collarPhi])⟩

end

end Work.Milnor
