import Mathlib
import Submission.Work.PieceHomology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The boundary `∂[-1,1]²` of the square is a circle

`Work.HomologyIso.BdryPt = {p : [-1,1]² // ‖p‖∞ = 1}` is the boundary of the square of the filling
pieces, i.e. topologically the circle.  We produce here an explicit homeomorphism with
`AddCircle (1 : ℝ)`, as the round trip

`∂[-1,1]²  ⟶  S¹ ⊆ ℝ² ≅ ℂ  ⟶  AddCircle 1`

where the first arrow is the radial projection `p ↦ ‖p‖∞⁻¹ • p` onto the Euclidean unit circle and
the second is the standard parametrisation `Circle ≃ₜ AddCircle T` of Mathlib.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Work.Space

namespace Work.PieceHomology

noncomputable section

/-! ## §1  `ℂ` and the Euclidean plane `ℝ²` -/

/-- The linear isometry `ℂ ≅ ℝ²` sending `z` to `(z.re, z.im)`, for the Euclidean (`ℓ²`) norm. -/
def toE (z : ℂ) : E2 := Complex.orthonormalBasisOneI.repr z

/-- The inverse linear isometry `ℝ² ≅ ℂ`. -/
def toC (p : E2) : ℂ := Complex.orthonormalBasisOneI.repr.symm p

lemma continuous_toE : Continuous toE := LinearIsometryEquiv.continuous _

lemma continuous_toC : Continuous toC := LinearIsometryEquiv.continuous _

lemma toE_smul (c : ℝ) (z : ℂ) : toE (c • z) = c • toE z :=
  LinearIsometryEquiv.map_smul (e := Complex.orthonormalBasisOneI.repr) c z

lemma toC_smul (c : ℝ) (p : E2) : toC (c • p) = c • toC p :=
  LinearIsometryEquiv.map_smul (e := Complex.orthonormalBasisOneI.repr.symm) c p

lemma toC_toE (z : ℂ) : toC (toE z) = z :=
  LinearIsometryEquiv.symm_apply_apply Complex.orthonormalBasisOneI.repr z

lemma toE_toC (p : E2) : toE (toC p) = p :=
  LinearIsometryEquiv.apply_symm_apply Complex.orthonormalBasisOneI.repr p

lemma norm_toC (p : E2) : ‖toC p‖ = ‖p‖ := LinearIsometryEquiv.norm_map _ p

/-- The sup norm is computed on the coordinates of `toE z`. -/
lemma nrm_toE (z : ℂ) : nrm (toE z) = max |z.re| |z.im| := rfl

/-! ## §2  The radial projections -/

lemma abs_apply_le_nrm (w : E2) (i : Fin 2) : |w i| ≤ nrm w := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma nrm_inv_smul_le_one {w : E2} (hw : nrm w ≠ 0) (i : Fin 2) :
    |((nrm w)⁻¹ • w) i| ≤ 1 := by
  have hpos' : 0 ≤ (nrm w)⁻¹ := inv_nonneg.mpr (nrm_nonneg w)
  have h1 : |((nrm w)⁻¹ • w) i| = (nrm w)⁻¹ * |w i| := by
    show |(nrm w)⁻¹ * w.ofLp i| = (nrm w)⁻¹ * |w.ofLp i|
    rw [abs_mul, abs_of_nonneg hpos']
  rw [h1]
  calc (nrm w)⁻¹ * |w i| ≤ (nrm w)⁻¹ * nrm w :=
        mul_le_mul_of_nonneg_left (abs_apply_le_nrm w i) hpos'
    _ = 1 := inv_mul_cancel₀ hw

/-- The radial projection of `w` onto `∂[-1,1]²` for the sup norm, `w ↦ ‖w‖∞⁻¹ • w`. -/
def projSq (w : E2) (hw : nrm w ≠ 0) : Work.HomologyIso.BdryPt :=
  ⟨⟨(nrm w)⁻¹ • w, ⟨nrm_inv_smul_le_one hw 0, nrm_inv_smul_le_one hw 1⟩⟩, by
    show nrm ((nrm w)⁻¹ • w) = 1
    rw [Work.Space.nrm_smul (inv_nonneg.mpr (nrm_nonneg w)), inv_mul_cancel₀ hw]⟩

/-- The radial projection of `w` onto the unit circle of `ℂ`, `w ↦ ‖w‖⁻¹ • w`. -/
def projC (w : ℂ) (hw : ‖w‖ ≠ 0) : Circle :=
  ⟨(‖w‖)⁻¹ • w, by
    change (‖w‖)⁻¹ • w ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ hw]⟩

@[simp] lemma projSq_val (w : E2) (hw : nrm w ≠ 0) :
    ((projSq w hw : Work.HomologyIso.BdryPt) : E2) = (nrm w)⁻¹ • w := rfl

@[simp] lemma projC_val (w : ℂ) (hw : ‖w‖ ≠ 0) :
    ((projC w hw : Circle) : ℂ) = (‖w‖)⁻¹ • w := rfl

/-- A point of the unit circle of `ℂ` has nonzero sup norm in the plane. -/
lemma nrm_toE_ne_zero (z : Circle) : nrm (toE (z : ℂ)) ≠ 0 := by
  intro h
  have hre : (z : ℂ).re = 0 := by
    have hle : |(z : ℂ).re| ≤ nrm (toE (z : ℂ)) := by rw [nrm_toE]; exact le_max_left _ _
    rw [h] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have him : (z : ℂ).im = 0 := by
    have hle : |(z : ℂ).im| ≤ nrm (toE (z : ℂ)) := by rw [nrm_toE]; exact le_max_right _ _
    rw [h] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hz : (z : ℂ) = 0 := Complex.ext hre him
  have h1 := Circle.norm_coe z
  rw [hz, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- A boundary point of the square is nonzero, so its Euclidean norm is nonzero. -/
lemma norm_toC_ne_zero (p : Work.HomologyIso.BdryPt) :
    ‖toC (((p : SquarePt) : E2))‖ ≠ 0 := by
  rw [norm_toC]
  intro h
  have hp : ((p : SquarePt) : E2) = 0 := norm_eq_zero.mp h
  have hs : sqNorm (p : SquarePt) = 0 := by
    show nrm ((p : SquarePt) : E2) = 0
    rw [hp]; simp [Work.Space.nrm]
  rw [p.2] at hs
  exact one_ne_zero hs

/-! ## §3  The two directions of the homeomorphism -/

/-- `S¹ → ∂[-1,1]²`: send `z` to the boundary point of the square in the direction `z`. -/
def rho (z : Circle) : Work.HomologyIso.BdryPt := projSq (toE (z : ℂ)) (nrm_toE_ne_zero z)

/-- `∂[-1,1]² → S¹`: send `p` to the unit vector in the Euclidean direction of `p`. -/
def sigma (p : Work.HomologyIso.BdryPt) : Circle :=
  projC (toC (((p : SquarePt) : E2))) (norm_toC_ne_zero p)

@[simp] lemma rho_val (z : Circle) :
    (((rho z : Work.HomologyIso.BdryPt) : SquarePt) : E2)
      = (nrm (toE (z : ℂ)))⁻¹ • toE (z : ℂ) := rfl

@[simp] lemma sigma_val (p : Work.HomologyIso.BdryPt) :
    ((sigma p : Circle) : ℂ)
      = (‖toC (((p : SquarePt) : E2))‖)⁻¹ • toC (((p : SquarePt) : E2)) := rfl

lemma sigma_rho (z : Circle) : sigma (rho z) = z := by
  apply Subtype.ext
  rw [sigma_val, rho_val, toC_smul, toC_toE]
  have hnorm : ‖(nrm (toE (z : ℂ)))⁻¹ • (z : ℂ)‖ = (nrm (toE (z : ℂ)))⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (nrm_nonneg _)),
      Circle.norm_coe, mul_one]
  rw [hnorm, inv_inv, smul_smul, mul_inv_cancel₀ (nrm_toE_ne_zero z), one_smul]

lemma rho_sigma (p : Work.HomologyIso.BdryPt) : rho (sigma p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  rw [rho_val, sigma_val, toE_smul, toE_toC]
  have hq : nrm (((p : SquarePt) : E2)) = 1 := p.2
  have hnorm : nrm ((‖toC (((p : SquarePt) : E2))‖)⁻¹ • ((p : SquarePt) : E2))
      = (‖toC (((p : SquarePt) : E2))‖)⁻¹ := by
    rw [Work.Space.nrm_smul (inv_nonneg.mpr (norm_nonneg _)), hq, mul_one]
  rw [hnorm, inv_inv, smul_smul, mul_inv_cancel₀ (norm_toC_ne_zero p), one_smul]

/-! ## §4  Continuity and the homeomorphism -/

lemma continuous_rho_bdryPt : Continuous rho := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun z : Circle => (nrm (toE (z : ℂ)))⁻¹ :=
    (Work.Space.continuous_nrm.comp (continuous_toE.comp continuous_subtype_val)).inv₀
      (fun z => nrm_toE_ne_zero z)
  exact h1.smul (continuous_toE.comp continuous_subtype_val)

lemma continuous_sigma_circle : Continuous sigma := by
  refine Continuous.subtype_mk ?_ _
  have hsub : Continuous fun p : Work.HomologyIso.BdryPt => ((p : SquarePt) : E2) :=
    Continuous.comp (g := fun q : SquarePt => (q : E2))
      (f := fun p : Work.HomologyIso.BdryPt => (p : SquarePt)) continuous_subtype_val
      continuous_subtype_val
  have h1 : Continuous fun p : Work.HomologyIso.BdryPt => (‖toC (((p : SquarePt) : E2))‖)⁻¹ :=
    ((continuous_norm.comp (continuous_toC.comp hsub))).inv₀ (fun p => norm_toC_ne_zero p)
  exact h1.smul (continuous_toC.comp hsub)

/-- **The boundary of the square is the circle**: the radial projection
`S¹ ⊆ ℂ ≃ₜ ∂[-1,1]²`, with inverse the Euclidean radial projection. -/
def homeo : Circle ≃ₜ Work.HomologyIso.BdryPt where
  toFun := rho
  invFun := sigma
  left_inv := sigma_rho
  right_inv := rho_sigma
  continuous_toFun := continuous_rho_bdryPt
  continuous_invFun := continuous_sigma_circle

theorem homeomorph_bdryPt :
    Nonempty (Work.HomologyIso.BdryPt ≃ₜ AddCircle (1 : ℝ)) :=
  ⟨((AddCircle.homeomorphCircle (T := 1) one_ne_zero).trans homeo).symm⟩

end

end Work.PieceHomology
