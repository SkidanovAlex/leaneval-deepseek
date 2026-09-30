import Mathlib
import Submission.Work.Milnor.Model8
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.CollarHomotopy
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.exists_collar_coordinates
import Submission.Work.Glue.mdifferentiable_iota_smooth

set_option synthInstance.maxHeartbeats 400000

/-!
# The capping construction: definitions and elementary algebra

This file sets up the maps used to cap the disc bundle `Vk (-2)` by a disc, i.e. to build the
closed `8`-manifold `X = D(ξ) ∪_F D⁸` of `Submission/NOTES.md` §9.3 from a diffeomorphism
`e : Mk (-2) ≃ S⁷` of the sphere bundle with the unit sphere.

* `capExterior` — the exterior `{1/2 < ‖z‖}` of the ball of radius `1/2` in `ℝ⁸`, the piece glued
  to the collar;
* `unitOf z` — the point of `S⁷` in the direction of `z` (junk value at `z = 0`);
* `qDir y` — the point of `S³` in the direction of a quaternion `y` (junk value at `y = 0`);
* `capFun e` — the map `Vk (-2) → ℝ⁸` given on the collar by `p ↦ ν(p) • e(p/ν(p))`;
* `capFunInv e` — its inverse, `z ↦ ‖z‖ • mkToVkFun (e⁻¹ (z/‖z‖))`;
* `vkModelIso`-chartwise formulas for both maps.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor
open scoped Classical

noncomputable section

/-- The unit sphere `S⁷ ⊆ ℝ⁸`. -/
abbrev Sph8 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-- The exterior of the ball of radius `1/2` in `ℝ⁸`: the piece glued to the collar of `Vk (-2)`. -/
def capExterior : Set (EuclideanSpace ℝ (Fin 8)) := {z | 1 / 2 < ‖z‖}

theorem isOpen_capExterior : IsOpen capExterior := isOpen_lt continuous_const continuous_norm

theorem mem_capExterior_iff {z : EuclideanSpace ℝ (Fin 8)} :
    z ∈ capExterior ↔ 1 / 2 < ‖z‖ := Iff.rfl

/-- The exterior of the ball of radius `1/2`, as an open subset. -/
def capExteriorOpens : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 8)) where
  carrier := capExterior
  is_open' := isOpen_capExterior

theorem ne_zero_of_mem_capExterior {z : EuclideanSpace ℝ (Fin 8)} (h : z ∈ capExterior) :
    z ≠ 0 := by
  intro hz
  have h' : (1 : ℝ) / 2 < ‖z‖ := h
  rw [hz] at h'
  norm_num at h'

/-! ## The direction maps -/

/-- The point of `S⁷` in the direction of `z : ℝ⁸`; at `z = 0` we use the junk value
`EuclideanSpace.single 0 1`. -/
def unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8 :=
  if h : z = 0 then ⟨EuclideanSpace.single 0 1, by
      rw [Metric.mem_sphere, dist_zero_right]; simp⟩
    else ⟨‖z‖⁻¹ • z, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z)]
      field_simp⟩

/-- The underlying vector of `unitOf z`, for nonzero `z`. -/
@[simp] theorem coe_unitOf_of_ne {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) :
    ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)) = ‖z‖⁻¹ • z := by
  simp only [unitOf, dif_neg hz]

/-- The point of `S³` in the direction of a quaternion `y`; at `y = 0` we use the junk value `1`. -/
def qDir (y : Quaternion ℝ) : QS3 :=
  if h : y = 0 then ⟨1, by rw [Metric.mem_sphere, dist_zero_right, norm_one]⟩
    else ⟨‖y‖⁻¹ • y, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg y)]
      field_simp⟩

/-- The underlying quaternion of `qDir y`, for nonzero `y`. -/
@[simp] theorem coe_qDir_of_ne {y : Quaternion ℝ} (hy : y ≠ 0) :
    ((qDir y : QS3) : Quaternion ℝ) = ‖y‖⁻¹ • y := by
  simp only [qDir, dif_neg hy]

/-! ## The two maps -/

/-- **The capping map**: on the collar `{1/2 < ν}` of the disc bundle it is
`p ↦ ν(p) • e(p/ν(p))`, where `e : Mk (-2) ≃ S⁷` is the identification of the sphere bundle with
the unit sphere.  Off the collar it is the junk value `0`. -/
def capFun (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    Vk (-2) → EuclideanSpace ℝ (Fin 8) :=
  fun p => if h : p ∈ collar (-2) then
      (fibreNormFun (-2) p) • (e (collarPsi (-2) ⟨p, h⟩) : EuclideanSpace ℝ (Fin 8))
    else 0

/-- **The inverse of the capping map**: `z ↦ ‖z‖ • mkToVkFun (e⁻¹ (z/‖z‖))`.  Off the exterior it
is the junk value `ιX 0`. -/
def capFunInv (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    EuclideanSpace ℝ (Fin 8) → Vk (-2) :=
  fun z => if z ∈ capExterior then
      vScale (-2) ‖z‖ (mkToVkFun (-2) (e.symm (unitOf z)))
    else (vData (-2)).ιX 0

@[simp] theorem capFun_of_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) :
    capFun e p = (fibreNormFun (-2) p) •
      (e (collarPsi (-2) ⟨p, h⟩) : EuclideanSpace ℝ (Fin 8)) := dif_pos h

@[simp] theorem capFunInv_of_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (h : z ∈ capExterior) :
    capFunInv e z = vScale (-2) ‖z‖ (mkToVkFun (-2) (e.symm (unitOf z))) := dif_pos h

/-! ## Elementary membership and inverse laws -/

theorem capFun_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) : capFun e p ∈ capExterior := by
  rw [capFun_of_mem e h]
  show (1 : ℝ) / 2 < ‖(fibreNormFun (-2) p) • (e (collarPsi (-2) ⟨p, h⟩) :
    EuclideanSpace ℝ (Fin 8))‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by have := mem_collar.mp h; linarith),
    norm_eq_of_mem_sphere, mul_one]
  exact mem_collar.mp h

theorem capFunInv_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (h : z ∈ capExterior) : capFunInv e z ∈ collar (-2) := by
  rw [capFunInv_of_mem e h, mem_collar, fibreNormFun_vScale, fibreNormFun_mkToVkFun,
    mul_one, abs_of_nonneg (norm_nonneg z)]
  exact h

/-- The fibre norm of the normalisation of a collar point is one. -/
theorem fibreNormFun_collarNorm (k : ℤ) (p : ↥(collar k)) :
    fibreNormFun k ((collarNorm k p : {p : Vk k // fibreNormFun k p = 1}) : Vk k) = 1 :=
  (collarNorm k p).2

/-- The normalisation of a point of the sphere bundle of `Mk k` (scaled by `c > 0`) reads back as
the original point of `Mk k`. -/
theorem collarPsi_of_eq {k : ℤ} {p : Vk k} (hp : p ∈ collar k) {c : ℝ} (hc : 1 / 2 < c)
    {q : Mk k} (hpq : p = vScale k c (mkToVkFun k q)) : collarPsi k ⟨p, hp⟩ = q := by
  rw [collarPsi_apply]
  have h1 : (collarNorm k ⟨p, hp⟩ : {p : Vk k // fibreNormFun k p = 1})
      = ⟨mkToVkFun k q, fibreNormFun_mkToVkFun k q⟩ := by
    refine Subtype.ext ?_
    rw [collarNorm_coe]
    change vScale k (fibreNormFun k p)⁻¹ p = mkToVkFun k q
    rw [hpq, fibreNormFun_vScale_mkToVkFun k c (le_of_lt (by linarith)) q, vScale_mul,
      inv_mul_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < c)), vScale_one]
    rfl
  rw [h1, unitInv_mkToVkFun]

/-- The normalisation of a point of the sphere bundle of `Mk (-2)` is the point itself. -/
theorem collarPsi_mkToVkFun (q : Mk (-2)) :
    collarPsi (-2) ⟨mkToVkFun (-2) q,
      mem_collar.mpr (one_lt_fibreNorm_mkToVkFun (-2) q)⟩ = q := by
  rw [collarPsi_apply]
  have h1 : (collarNorm (-2) ⟨mkToVkFun (-2) q,
      mem_collar.mpr (one_lt_fibreNorm_mkToVkFun (-2) q)⟩
      : {p : Vk (-2) // fibreNormFun (-2) p = 1})
      = ⟨mkToVkFun (-2) q, fibreNormFun_mkToVkFun (-2) q⟩ := by
    refine Subtype.ext ?_
    rw [collarNorm_coe]
    simp only [Subtype.coe_mk, fibreNormFun_mkToVkFun (-2) q, inv_one, vScale_one]
    rfl
  rw [h1]
  exact unitInv_mkToVkFun (-2) q

/-- The capping map is the diffeomorphism `e` on the sphere bundle `Mk (-2)`. -/
theorem capFun_mkToVkFun (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (q : Mk (-2)) : capFun e (mkToVkFun (-2) q) = (e q : EuclideanSpace ℝ (Fin 8)) := by
  rw [capFun_of_mem e (mem_collar.mpr (one_lt_fibreNorm_mkToVkFun (-2) q))]
  simp only [Subtype.coe_mk, fibreNormFun_mkToVkFun (-2) q, one_smul]
  congr 2
  exact collarPsi_mkToVkFun q

theorem capFunInv_capFun (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) : capFunInv e (capFun e p) = p := by
  have hcap := capFun_mem e h
  have hnorm : ‖capFun e p‖ = fibreNormFun (-2) p := by
    rw [capFun_of_mem e h, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by have := mem_collar.mp h; linarith), norm_eq_of_mem_sphere, mul_one]
  have hne : fibreNormFun (-2) p ≠ 0 := by have := mem_collar.mp h; linarith
  have h0 : capFun e p ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm]
    exact hne
  have hunit : unitOf (capFun e p) = e (collarPsi (-2) ⟨p, h⟩) := by
    refine Subtype.ext ?_
    rw [coe_unitOf_of_ne h0]
    simp only [Subtype.coe_mk, hnorm]
    rw [capFun_of_mem e h, inv_smul_smul₀ hne]
  rw [capFunInv_of_mem e hcap, hnorm, hunit, e.symm_apply_apply, mkToVkFun_collarPsi,
    vScale_mul]
  rw [mul_inv_cancel₀ hne, vScale_one]
  rfl

theorem capFun_capFunInv (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (h : z ∈ capExterior) : capFun e (capFunInv e z) = z := by
  have hcollar := capFunInv_mem e h
  have hnorm : fibreNormFun (-2) (capFunInv e z) = ‖z‖ := by
    rw [capFunInv_of_mem e h, fibreNormFun_vScale, fibreNormFun_mkToVkFun, mul_one,
      abs_of_nonneg (norm_nonneg z)]
  rw [capFun_of_mem e hcollar, hnorm]
  have hpsi : collarPsi (-2) ⟨capFunInv e z, hcollar⟩ = e.symm (unitOf z) :=
    collarPsi_of_eq hcollar (by have h' : (1 : ℝ) / 2 < ‖z‖ := h; linarith)
      (capFunInv_of_mem e h)
  rw [hpsi, e.apply_symm_apply]
  rw [coe_unitOf_of_ne (ne_zero_of_mem_capExterior h), smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ne_zero_of_mem_capExterior h)), one_smul]

/-! ## The chartwise formulas -/

/-- **The first chart of the normalisation.**  On the first chart of the disc bundle, the collar
retraction is the fibrewise normalisation, read off as a point of the sphere bundle `Mk (-2)`. -/
theorem collarPsi_ιX (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    collarPsi (-2) ⟨(vData (-2)).ιX a,
        mem_collar.mpr (by rw [fibreNormFun_ιX]; exact ha)⟩
      = (clutchData (-2)).ιX (a.1, qDir a.2) := by
  have hne : a.2 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha
    norm_num at ha
  apply mkToVkFun_injective (-2)
  rw [mkToVkFun_collarPsi]
  change vScale (-2) (fibreNormFun (-2) ((vData (-2)).ιX a))⁻¹ ((vData (-2)).ιX a)
    = mkToVkFun (-2) ((clutchData (-2)).ιX (a.1, qDir a.2))
  rw [mkToVk_ιX, vScale_ιX, fibreNormFun_ιX]
  show (vData (-2)).ιX (a.1, ‖a.2‖⁻¹ • a.2)
    = (vData (-2)).ιX (a.1, ((qDir a.2 : QS3) : Quaternion ℝ))
  congr 1
  exact Prod.ext rfl (by rw [coe_qDir_of_ne hne])

/-- **The second chart of the normalisation.** -/
theorem collarPsi_ιY (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    collarPsi (-2) ⟨(vData (-2)).ιY a,
        mem_collar.mpr (by rw [fibreNormFun_ιY]; exact ha)⟩
      = (clutchData (-2)).ιY (a.1, qDir a.2) := by
  have hne : a.2 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha
    norm_num at ha
  apply mkToVkFun_injective (-2)
  rw [mkToVkFun_collarPsi]
  change vScale (-2) (fibreNormFun (-2) ((vData (-2)).ιY a))⁻¹ ((vData (-2)).ιY a)
    = mkToVkFun (-2) ((clutchData (-2)).ιY (a.1, qDir a.2))
  rw [mkToVk_ιY, vScale_ιY, fibreNormFun_ιY]
  show (vData (-2)).ιY (a.1, ‖a.2‖⁻¹ • a.2)
    = (vData (-2)).ιY (a.1, ((qDir a.2 : QS3) : Quaternion ℝ))
  congr 1
  exact Prod.ext rfl (by rw [coe_qDir_of_ne hne])

/-- **The first chart of the capping map.**  For `a : ℝ⁴ × ℍ` with `‖a.2‖ > 1/2`, the capping map
on the first chart of the disc bundle is multiplication by `‖a.2‖` of the value of `e` on the
normalised point. -/
theorem capFun_ιX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFun e ((vData (-2)).ιX a) = ‖a.2‖ •
      (e ((clutchData (-2)).ιX (a.1, qDir a.2)) : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : (vData (-2)).ιX a ∈ collar (-2) :=
    mem_collar.mpr (by rw [fibreNormFun_ιX]; exact ha)
  calc capFun e ((vData (-2)).ιX a)
      = fibreNormFun (-2) ((vData (-2)).ιX a) •
          (e (collarPsi (-2) ⟨(vData (-2)).ιX a, hmem⟩)
            : EuclideanSpace ℝ (Fin 8)) := capFun_of_mem e hmem
    _ = ‖a.2‖ • (e (collarPsi (-2) ⟨(vData (-2)).ιX a, hmem⟩)
            : EuclideanSpace ℝ (Fin 8)) := by rw [fibreNormFun_ιX]
    _ = ‖a.2‖ • (e ((clutchData (-2)).ιX (a.1, qDir a.2))
            : EuclideanSpace ℝ (Fin 8)) := by rw [collarPsi_ιX a ha]

/-- **The second chart of the capping map.** -/
theorem capFun_ιY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFun e ((vData (-2)).ιY a) = ‖a.2‖ •
      (e ((clutchData (-2)).ιY (a.1, qDir a.2)) : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : (vData (-2)).ιY a ∈ collar (-2) :=
    mem_collar.mpr (by rw [fibreNormFun_ιY]; exact ha)
  calc capFun e ((vData (-2)).ιY a)
      = fibreNormFun (-2) ((vData (-2)).ιY a) •
          (e (collarPsi (-2) ⟨(vData (-2)).ιY a, hmem⟩)
            : EuclideanSpace ℝ (Fin 8)) := capFun_of_mem e hmem
    _ = ‖a.2‖ • (e (collarPsi (-2) ⟨(vData (-2)).ιY a, hmem⟩)
            : EuclideanSpace ℝ (Fin 8)) := by rw [fibreNormFun_ιY]
    _ = ‖a.2‖ • (e ((clutchData (-2)).ιY (a.1, qDir a.2))
            : EuclideanSpace ℝ (Fin 8)) := by rw [collarPsi_ιY a ha]

/-- **The first chart of the inverse capping map.**  If `e⁻¹ (z/‖z‖)` lies in the first chart of
`Mk (-2)`, with chart coordinates `p`, then the inverse capping map sends `z` to the point of the
disc bundle whose first chart coordinates are `(p.1, ‖z‖ • p.2)`. -/
theorem capFunInv_eq_ιX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ∈ capExterior) {p : MSpace}
    (hp : e.symm (unitOf z) = (clutchData (-2)).ιX p) :
    capFunInv e z = (vData (-2)).ιX (p.1, ‖z‖ • (p.2 : Quaternion ℝ)) := by
  rw [capFunInv_of_mem e hz, hp, mkToVk_ιX, vScale_ιX]

/-- **The second chart of the inverse capping map.** -/
theorem capFunInv_eq_ιY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ∈ capExterior) {p : MSpace}
    (hp : e.symm (unitOf z) = (clutchData (-2)).ιY p) :
    capFunInv e z = (vData (-2)).ιY (p.1, ‖z‖ • (p.2 : Quaternion ℝ)) := by
  rw [capFunInv_of_mem e hz, hp, mkToVk_ιY, vScale_ιY]

/-! ## The chartwise formulas as functions -/

/-- The explicit first-chart formula for the capping map: read off the chart coordinates `a` of a
point of the disc bundle, normalise the fibre coordinate and apply `e`, then scale by `‖a.2‖`. -/
def chartFormX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) : MSpace8 :=
  ‖a.2‖ • (vkModelIso.symm
    ((e ((clutchData (-2)).ιX (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))

/-- The explicit second-chart formula for the capping map. -/
def chartFormY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) : MSpace8 :=
  ‖a.2‖ • (vkModelIso.symm
    ((e ((clutchData (-2)).ιY (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))

/-- The explicit first-chart formula for the inverse capping map: read the point of `S⁷` in the
direction of `w`, apply `e⁻¹`, read off its first-chart coordinates in `Mk (-2)` and scale the
fibre coordinate by `‖w‖`. -/
def chartInvFormX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (w : MSpace8) : MSpace8 :=
  (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).1,
    ‖vkModelIso w‖ • ((((clutchData (-2)).homX.symm
      (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ))

/-- The explicit second-chart formula for the inverse capping map. -/
def chartInvFormY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (w : MSpace8) : MSpace8 :=
  (((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).1,
    ‖vkModelIso w‖ • ((((clutchData (-2)).homY.symm
      (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ))

/-- The capping map on the first chart is `vkModelIso` of the explicit first-chart formula. -/
theorem capFun_ιX' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFun e ((vData (-2)).ιX a) = vkModelIso (chartFormX e a) := by
  rw [capFun_ιX e a ha, chartFormX, map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- The capping map on the second chart is `vkModelIso` of the explicit second-chart formula. -/
theorem capFun_ιY' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFun e ((vData (-2)).ιY a) = vkModelIso (chartFormY e a) := by
  rw [capFun_ιY e a ha, chartFormY, map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse capping map on the first chart is `ιX` of the explicit first-chart formula. -/
theorem capFunInv_eq_ιX' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {w : MSpace8} (hz : vkModelIso w ∈ capExterior)
    (hw : e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX) :
    capFunInv e (vkModelIso w) = (vData (-2)).ιX (chartInvFormX e w) := by
  obtain ⟨p, hp⟩ := hw
  have hpair : ((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))) = p := by
    rw [← hp]
    exact (clutchData (-2)).homX_symm_apply p
  rw [capFunInv_eq_ιX e hz hp.symm]
  have hval : chartInvFormX e w
      = (p.1, ‖vkModelIso w‖ • ((p.2 : QS3) : Quaternion ℝ)) := by
    rw [chartInvFormX, hpair]
  rw [hval]

/-- The inverse capping map on the second chart is `ιY` of the explicit second-chart formula. -/
theorem capFunInv_eq_ιY' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {w : MSpace8} (hz : vkModelIso w ∈ capExterior)
    (hw : e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY) :
    capFunInv e (vkModelIso w) = (vData (-2)).ιY (chartInvFormY e w) := by
  obtain ⟨p, hp⟩ := hw
  have hpair : ((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))) = p := by
    rw [← hp]
    exact (clutchData (-2)).homY_symm_apply p
  rw [capFunInv_eq_ιY e hz hp.symm]
  have hval : chartInvFormY e w
      = (p.1, ‖vkModelIso w‖ • ((p.2 : QS3) : Quaternion ℝ)) := by
    rw [chartInvFormY, hpair]
  rw [hval]


/-! ## Abbreviations of the model with corners, for use in statements

The delegation harness writes statements in a file without the scoped notations `𝓡`, `𝓘` and `∞`
open, so we provide plain names for the models used below. -/

/-- The product model `ℝ⁴ × S³`. -/
abbrev mE4E3 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)) :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))

/-- The self model on `ℝ⁸`. -/
abbrev mE8 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin 8)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8))

/-- The self model on `ℝ⁴ × ℍ`, the model space of the disc bundle. -/
abbrev mMSpace8 : ModelWithCorners ℝ MSpace8 MSpace8 := modelWithCornersSelf ℝ MSpace8

/-- The self model on `ℝ⁷`. -/
abbrev mE7 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 7)) (EuclideanSpace ℝ (Fin 7)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 7))

/-- The smoothness level `∞`. -/
abbrev smLevel : WithTop ENat := ∞

/-! ## Smoothness of the normalisation maps -/

/-- The set `{a : ℝ⁴ × ℍ | a.2 ≠ 0}`, as an open subset. -/
def capFibreOpens : TopologicalSpace.Opens MSpace8 where
  carrier := {a : MSpace8 | a.2 ≠ 0}
  is_open' := isOpen_ne_fun continuous_snd continuous_const

/-- The fibrewise normalisation `a ↦ a.2/‖a.2‖` is smooth, as a map into `S³`. -/
theorem contMDiffOn_qDir_snd :
    ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞ (fun a : MSpace8 => qDir a.2) capFibreOpens := by
  have hdiff : ContDiffOn ℝ ∞ (fun a : MSpace8 => ‖a.2‖⁻¹ • a.2) (capFibreOpens : Set MSpace8) := by
    have hs : ContDiffOn ℝ ∞ (fun a : MSpace8 => a.2) (capFibreOpens : Set MSpace8) :=
      contDiff_snd.contDiffOn
    have hn : ContDiffOn ℝ ∞ (fun a : MSpace8 => ‖a.2‖) (capFibreOpens : Set MSpace8) :=
      ContDiffOn.norm ℝ hs (fun a ha => ha)
    exact (hn.inv (fun a ha => norm_ne_zero_iff.mpr ha)).smul hs
  have hcoe : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun a : MSpace8 => ((qDir a.2 : QS3) : Quaternion ℝ)) (capFibreOpens : Set MSpace8) :=
    (contMDiffOn_iff_contDiffOn.mpr hdiff).congr (fun a ha => coe_qDir_of_ne ha)
  have hglob : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun a : ↥capFibreOpens => ((qDir (a : MSpace8).2 : QS3) : Quaternion ℝ)) := by
    intro a
    exact (contMDiffAt_subtype_iff (U := capFibreOpens)
      (f := fun a : MSpace8 => ((qDir a.2 : QS3) : Quaternion ℝ)) (x := a)).mpr
      (hcoe.contMDiffAt (capFibreOpens.2.mem_nhds a.2))
  have hmem : ∀ a : ↥capFibreOpens,
      ((qDir (a : MSpace8).2 : QS3) : Quaternion ℝ) ∈ Metric.sphere (0 : Quaternion ℝ) 1 :=
    fun a => (qDir _).2
  have hsphere : ContMDiff 𝓘(ℝ, MSpace8) (𝓡 3) ∞ (fun a : ↥capFibreOpens => qDir (a : MSpace8).2) :=
    (ContMDiff.codRestrict_sphere (n := 3) hglob hmem).congr (fun a => Subtype.ext rfl)
  intro a ha
  exact ((contMDiffAt_subtype_iff (U := capFibreOpens) (f := fun a : MSpace8 => qDir a.2)
    (x := ⟨a, ha⟩)).mp (hsphere ⟨a, ha⟩)).contMDiffWithinAt

/-- The direction map `z ↦ z/‖z‖` is smooth on the exterior of the ball of radius `1/2`,
as a map into `S⁷`. -/
theorem contMDiffOn_unitOf :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞ (fun z => unitOf z) capExterior := by
  have hdiff : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖⁻¹ • z) capExterior := by
    have hs : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => z) capExterior :=
      contDiff_id.contDiffOn
    have hn : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖) capExterior :=
      ContDiffOn.norm ℝ hs (fun z hz => ne_zero_of_mem_capExterior hz)
    exact (hn.inv (fun z hz => norm_ne_zero_iff.mpr (ne_zero_of_mem_capExterior hz))).smul hs
  have hcoe : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      capExterior :=
    (contMDiffOn_iff_contDiffOn.mpr hdiff).congr (fun z hz => coe_unitOf_of_ne
      (ne_zero_of_mem_capExterior hz))
  have hglob : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : ↥capExteriorOpens => ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8)
        : EuclideanSpace ℝ (Fin 8))) := by
    intro z
    exact (contMDiffAt_subtype_iff (U := capExteriorOpens)
      (f := fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      (x := z)).mpr (hcoe.contMDiffAt (capExteriorOpens.2.mem_nhds z.2))
  have hmem : ∀ z : ↥capExteriorOpens,
      ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8) : EuclideanSpace ℝ (Fin 8))
        ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 := fun z => (unitOf _).2
  have hsphere : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞
      (fun z : ↥capExteriorOpens => unitOf (z : EuclideanSpace ℝ (Fin 8))) :=
    (ContMDiff.codRestrict_sphere (n := 7) hglob hmem).congr (fun z => Subtype.ext rfl)
  intro z hz
  exact ((contMDiffAt_subtype_iff (U := capExteriorOpens)
    (f := fun z : EuclideanSpace ℝ (Fin 8) => unitOf z) (x := ⟨z, hz⟩)).mp
    (hsphere ⟨z, hz⟩)).contMDiffWithinAt

/-! ## The linear isometry `vkModelIso`, and the model structure it induces on `ℝ⁸` -/

theorem extChartAt_pushed_eq (y : EuclideanSpace ℝ (Fin 8)) :
    ⇑(extChartAt 𝓘(ℝ, MSpace8) y) = ⇑vkModelIso.symm := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe, Work.Morse.pushChartedSpace_chartAt,
    Work.Morse.pushChart, chartAt_self_eq, OpenPartialHomeomorph.refl_trans]
  funext z
  rw [Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_apply, Work.Morse.modelHomeo_apply,
    modelWithCornersSelf_coe]
  rfl

theorem extChartAt_pushed_symm_eq (y : EuclideanSpace ℝ (Fin 8)) :
    ⇑((extChartAt 𝓘(ℝ, MSpace8) y).symm) = ⇑vkModelIso := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, Work.Morse.pushChartedSpace_chartAt,
    Work.Morse.pushChart, chartAt_self_eq, OpenPartialHomeomorph.refl_trans]
  funext z
  rw [Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    Work.Morse.modelHomeo_symm_apply, ContinuousLinearEquiv.symm_symm,
    modelWithCornersSelf_coe_symm]
  rfl

theorem extChartAt_self_coe (w : MSpace8) :
    ⇑(extChartAt 𝓘(ℝ, MSpace8) w) = (id : MSpace8 → MSpace8) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  funext z
  rw [Function.comp_apply, modelWithCornersSelf_coe]
  rfl

theorem extChartAt_self_symm_coe (w : MSpace8) :
    ⇑((extChartAt 𝓘(ℝ, MSpace8) w).symm) = (id : MSpace8 → MSpace8) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply]
  funext z
  rw [Function.comp_apply, modelWithCornersSelf_coe_symm]
  rfl

/-- The linear isometry `MSpace8 ≃ ℝ⁸` is smooth (for the standard model structure on `ℝ⁸`). -/
theorem contMDiff_vkModelIso :
    ContMDiff mMSpace8 mE8 smLevel (fun w : MSpace8 => vkModelIso w) :=
  (vkModelIso : MSpace8 →L[ℝ] EuclideanSpace ℝ (Fin 8)).contMDiff

/-- The linear isometry `MSpace8 ≃ ℝ⁸` is smooth when `ℝ⁸` carries the model structure pushed
forward from the standard one. -/
theorem contMDiff_vkModelIso_pushed :
    ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ (fun w : MSpace8 => vkModelIso w) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨vkModelIso.continuous.continuousAt, ?_⟩
  have hfun : (⇑(extChartAt 𝓘(ℝ, MSpace8) (vkModelIso w)) ∘ (fun w : MSpace8 => vkModelIso w)
      ∘ ⇑(extChartAt 𝓘(ℝ, MSpace8) w).symm) = (id : MSpace8 → MSpace8) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, extChartAt_pushed_eq, extChartAt_self_symm_coe]
    show vkModelIso.symm (vkModelIso z) = z
    exact vkModelIso.symm_apply_apply z
  rw [hfun]
  exact contDiffWithinAt_id

/-- The inverse of that isometry, from `ℝ⁸` (with the pushed model structure) back to `MSpace8`,
is smooth. -/
theorem contMDiff_vkModelIsoSymm_pushed :
    ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞
      (fun y : EuclideanSpace ℝ (Fin 8) => vkModelIso.symm y) := by
  intro y
  rw [contMDiffAt_iff]
  refine ⟨vkModelIso.symm.continuous.continuousAt, ?_⟩
  have hfun : (⇑(extChartAt 𝓘(ℝ, MSpace8) (vkModelIso.symm y))
      ∘ (fun y : EuclideanSpace ℝ (Fin 8) => vkModelIso.symm y)
      ∘ ⇑(extChartAt 𝓘(ℝ, MSpace8) y).symm) = (id : MSpace8 → MSpace8) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, extChartAt_self_coe, extChartAt_pushed_symm_eq]
    show vkModelIso.symm (vkModelIso z) = z
    exact vkModelIso.symm_apply_apply z
  rw [hfun]
  exact contDiffWithinAt_id

/-! ## Smoothness of the two gluing charts -/

theorem contMDiff_iotaX (k : ℤ) :
    ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ ((vData k).ιX) := by
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := 𝓘(ℝ, MSpace8)) (n := ∞)
    (f := (vData k).homX)).mp (Work.Glue.liftProp_homX_gen (vData k))
  have h1 : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ (⇑(vData k).homX) :=
    contMDiffOn_univ.mp (h.1.mono (by rw [Submission.Glue.Data.homX_source]))
  rw [← Work.Glue.homX_coe (vData k)]
  exact h1

theorem contMDiff_iotaY (k : ℤ) :
    ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ ((vData k).ιY) := by
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := 𝓘(ℝ, MSpace8)) (n := ∞)
    (f := (vData k).homY)).mp (Work.Glue.liftProp_homY_gen (vData k))
  have h1 : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ (⇑(vData k).homY) :=
    contMDiffOn_univ.mp (h.1.mono (by rw [Submission.Glue.Data.homY_source]))
  rw [← Work.Glue.homY_coe (vData k)]
  exact h1

theorem contMDiffOn_homXsymm (k : ℤ) :
    ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ (⇑((vData k).homX).symm)
      ((vData k).homX.target) :=
  ((isLocalStructomorphOn_contDiffGroupoid_iff (I := 𝓘(ℝ, MSpace8)) (n := ∞)
    (f := (vData k).homX)).mp (Work.Glue.liftProp_homX_gen (vData k))).2

theorem contMDiffOn_homYsymm (k : ℤ) :
    ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, MSpace8) ∞ (⇑((vData k).homY).symm)
      ((vData k).homY.target) :=
  ((isLocalStructomorphOn_contDiffGroupoid_iff (I := 𝓘(ℝ, MSpace8)) (n := ∞)
    (f := (vData k).homY)).mp (Work.Glue.liftProp_homY_gen (vData k))).2

theorem contMDiff_clutchIotaX (k : ℤ) :
    ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ ((clutchData k).ιX) := by
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := (𝓡 4).prod (𝓡 3)) (n := ∞)
    (f := (clutchData k).homX)).mp (Work.Glue.liftProp_homX_gen (clutchData k))
  have h1 : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑(clutchData k).homX) :=
    contMDiffOn_univ.mp (h.1.mono (by rw [Submission.Glue.Data.homX_source]))
  rw [← Work.Glue.homX_coe (clutchData k)]
  exact h1

theorem contMDiff_clutchIotaY (k : ℤ) :
    ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ ((clutchData k).ιY) := by
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := (𝓡 4).prod (𝓡 3)) (n := ∞)
    (f := (clutchData k).homY)).mp (Work.Glue.liftProp_homY_gen (clutchData k))
  have h1 : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑(clutchData k).homY) :=
    contMDiffOn_univ.mp (h.1.mono (by rw [Submission.Glue.Data.homY_source]))
  rw [← Work.Glue.homY_coe (clutchData k)]
  exact h1

theorem contMDiffOn_clutchHomXsymm (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑((clutchData k).homX).symm)
      ((clutchData k).homX.target) :=
  ((isLocalStructomorphOn_contDiffGroupoid_iff (I := (𝓡 4).prod (𝓡 3)) (n := ∞)
    (f := (clutchData k).homX)).mp (Work.Glue.liftProp_homX_gen (clutchData k))).2

theorem contMDiffOn_clutchHomYsymm (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑((clutchData k).homY).symm)
      ((clutchData k).homY.target) :=
  ((isLocalStructomorphOn_contDiffGroupoid_iff (I := (𝓡 4).prod (𝓡 3)) (n := ∞)
    (f := (clutchData k).homY)).mp (Work.Glue.liftProp_homY_gen (clutchData k))).2

end

end Work.Milnor
