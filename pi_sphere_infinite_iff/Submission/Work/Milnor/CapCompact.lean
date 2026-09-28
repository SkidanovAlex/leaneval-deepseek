import Mathlib
import Submission.Work.Milnor.CapDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# The **compact** capping of the disc bundle: definitions and elementary algebra

`Submission/Work/Milnor/Model8.lean` and `Submission/Work/Milnor/exists_capData.lean` build the
gluing datum of `Submission/NOTES.md` §9.3, in which the collar `{1/2 < ν} ⊆ Vk (-2)` is glued to
the *exterior* `{1/2 < ‖z‖} ⊆ ℝ⁸` of a ball, by the radius-preserving map `p ↦ ν(p) • e(p/ν(p))`.
That glued space is **not compact** (`NOTES.md` §9.8): the points with `ν → ∞` have no convergent
subsequence.

Here we use instead the **inverting** radius function `r(ν) = (ν - 1/2)⁻¹`, which maps the collar
`{1/2 < ν}` bijectively onto `ℝ⁸ ∖ {0}`, so that the far end `ν → ∞` of the collar accumulates at
the *origin* of `ℝ⁸` (a point of the second piece) rather than escaping.  Concretely

* `capPunct = ℝ⁸ ∖ {0}` — the open piece glued to the collar;
* `capFunK e p = (ν p - 1/2)⁻¹ • e(ψ p)` for `p ∈ collar (-2)`, where `ψ = collarPsi (-2)` is the
  normalisation of the collar onto the sphere bundle `Mk (-2)` and `e : Mk (-2) ≃ S⁷` is the
  capping diffeomorphism; the map is bijective onto `capPunct`, with inverse
* `capFunInvK e z = (‖z‖⁻¹ + 1/2) • mkToVkFun (e.symm (z/‖z‖))` for `z ≠ 0`;
* `capPhiK e` — the resulting open partial homeomorphism `Vk (-2) ⇢ ℝ⁸`.

The glued space `(Vk (-2) ⊔ ℝ⁸)/~` is then the closed `8`-manifold `X = D(ξ) ∪_e D⁸`: its two
compact cores are the disc bundle `{ν ≤ 1} ⊆ Vk (-2)` and the ball `{‖z‖ ≤ 2} ⊆ ℝ⁸`, and the glued
collar closes up around the origin of `ℝ⁸`.  (Proofs that the glued space is a compact, Hausdorff,
connected topological space are in `Submission/Work/Milnor/CapCompactData.lean` and its
companions.)

The predicate `IsCompactCapping e D` says that a gluing datum `D` is *this* datum (its open sets
are the collar and the punctured space, and its gluing map is `capFunK e`); every statement about
the compact capping `X` is phrased for a datum satisfying it.
-/

set_option linter.unusedVariables false

namespace Work.Milnor

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor
open scoped Classical

noncomputable section

/-! ## The punctured space `ℝ⁸ ∖ {0}` -/

/-- The punctured space `ℝ⁸ ∖ {0}`, the piece glued to the collar of `Vk (-2)`. -/
def capPunct : Set (EuclideanSpace ℝ (Fin 8)) := {z | z ≠ 0}

theorem isOpen_capPunct : IsOpen capPunct := by
  rw [capPunct]
  rw [show {z : EuclideanSpace ℝ (Fin 8) | z ≠ 0}
      = ({0} : Set (EuclideanSpace ℝ (Fin 8)))ᶜ from by ext z; simp]
  exact isOpen_compl_singleton

theorem mem_capPunct_iff {z : EuclideanSpace ℝ (Fin 8)} : z ∈ capPunct ↔ z ≠ 0 := Iff.rfl

theorem ne_zero_of_mem_capPunct {z : EuclideanSpace ℝ (Fin 8)} (h : z ∈ capPunct) : z ≠ 0 := h

/-- The punctured space, as an open subset. -/
def capPunctOpens : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 8)) where
  carrier := capPunct
  is_open' := isOpen_capPunct

/-! ## The two maps -/

/-- **The compact capping map**: on the collar `{1/2 < ν}` of the disc bundle it sends `p` to
`(ν p - 1/2)⁻¹ • e (ψ p)`, where `ψ` is the normalisation of the collar onto the sphere bundle
`Mk (-2)`.  Off the collar it is the junk value `0`. -/
def capFunK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    Vk (-2) → EuclideanSpace ℝ (Fin 8) :=
  fun p => if h : p ∈ collar (-2) then
      (fibreNormFun (-2) p - 1 / 2)⁻¹ • (e (collarPsi (-2) ⟨p, h⟩) : EuclideanSpace ℝ (Fin 8))
    else 0

/-- **The inverse of the compact capping map**: `z ↦ (‖z‖⁻¹ + 1/2) • mkToVkFun (e⁻¹ (z/‖z‖))`.
At `z = 0` it is the junk value `ιX 0`. -/
def capFunInvK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    EuclideanSpace ℝ (Fin 8) → Vk (-2) :=
  fun z => if h : z ≠ 0 then
      vScale (-2) (‖z‖⁻¹ + 1 / 2) (mkToVkFun (-2) (e.symm (unitOf z)))
    else (vData (-2)).ιX 0

@[simp] theorem capFunK_of_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) :
    capFunK e p = (fibreNormFun (-2) p - 1 / 2)⁻¹ •
      (e (collarPsi (-2) ⟨p, h⟩) : EuclideanSpace ℝ (Fin 8)) := dif_pos h

@[simp] theorem capFunInvK_of_ne (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (h : z ≠ 0) :
    capFunInvK e z = vScale (-2) (‖z‖⁻¹ + 1 / 2) (mkToVkFun (-2) (e.symm (unitOf z))) :=
  dif_pos h

/-! ## Elementary membership and inverse laws -/

theorem norm_capFunK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) :
    ‖capFunK e p‖ = (fibreNormFun (-2) p - 1 / 2)⁻¹ := by
  rw [capFunK_of_mem e h, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by have := mem_collar.mp h; linarith)),
    norm_eq_of_mem_sphere, mul_one]

theorem capFunK_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) : capFunK e p ∈ capPunct := by
  rw [mem_capPunct_iff, ← norm_ne_zero_iff, norm_capFunK e h]
  exact inv_ne_zero (by have := mem_collar.mp h; linarith)

theorem fibreNormFun_capFunInvK
    (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) :
    fibreNormFun (-2) (capFunInvK e z) = ‖z‖⁻¹ + 1 / 2 := by
  rw [capFunInvK_of_ne e hz, fibreNormFun_vScale, fibreNormFun_mkToVkFun, mul_one,
    abs_of_pos (by
      have : 0 < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz)
      linarith)]

theorem capFunInvK_mem (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) : capFunInvK e z ∈ collar (-2) := by
  rw [mem_collar, fibreNormFun_capFunInvK e hz]
  have : 0 < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz)
  linarith

/-- The direction of the value of the compact capping map is `e` applied to the direction of the
collar point. -/
theorem unitOf_capFunK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) :
    unitOf (capFunK e p) = e (collarPsi (-2) ⟨p, h⟩) := by
  have hpos : 0 < fibreNormFun (-2) p - 1 / 2 := by have := mem_collar.mp h; linarith
  have h0 : capFunK e p ≠ 0 := ne_zero_of_mem_capPunct (capFunK_mem e h)
  refine Subtype.ext ?_
  rw [coe_unitOf_of_ne h0, norm_capFunK e h, capFunK_of_mem e h, inv_inv,
    smul_inv_smul₀ (ne_of_gt hpos)]

/-- The normalisation of a value of the inverse capping map is `e.symm` of its direction. -/
theorem collarPsi_capFunInvK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) :
    collarPsi (-2) ⟨capFunInvK e z, capFunInvK_mem e hz⟩ = e.symm (unitOf z) := by
  refine collarPsi_of_eq (capFunInvK_mem e hz) (c := ‖z‖⁻¹ + 1 / 2) ?_ (capFunInvK_of_ne e hz)
  have : 0 < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz)
  linarith

theorem capFunInvK_capFunK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {p : Vk (-2)} (h : p ∈ collar (-2)) : capFunInvK e (capFunK e p) = p := by
  have hcap := capFunK_mem e h
  have hne : fibreNormFun (-2) p ≠ 0 := by have := mem_collar.mp h; linarith
  rw [capFunInvK_of_ne e (ne_zero_of_mem_capPunct hcap), norm_capFunK e h,
    unitOf_capFunK e h, e.symm_apply_apply, mkToVkFun_collarPsi (-2), vScale_mul, inv_inv,
    sub_add_cancel, mul_inv_cancel₀ hne, vScale_one]
  rfl

theorem capFunK_capFunInvK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) : capFunK e (capFunInvK e z) = z := by
  have hcollar := capFunInvK_mem e hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [capFunK_of_mem e hcollar, fibreNormFun_capFunInvK e hz, collarPsi_capFunInvK e hz,
    e.apply_symm_apply, add_sub_cancel_right, inv_inv, coe_unitOf_of_ne hz,
    smul_inv_smul₀ (ne_of_gt hpos)]

/-- On the unit sphere bundle `Mk (-2) ⊆ Vk (-2)` the compact capping map is `2 • e`. -/
theorem capFunK_mkToVkFun (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (q : Mk (-2)) :
    capFunK e (mkToVkFun (-2) q) = (2 : ℝ) • (e q : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : mkToVkFun (-2) q ∈ collar (-2) :=
    mem_collar.mpr (one_lt_fibreNorm_mkToVkFun (-2) q)
  have hpsi : collarPsi (-2) ⟨mkToVkFun (-2) q, hmem⟩ = q := collarPsi_mkToVkFun q
  rw [capFunK_of_mem e hmem, hpsi, fibreNormFun_mkToVkFun]
  norm_num

/-! ## Continuity -/

theorem continuousOn_capFunK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    ContinuousOn (capFunK e) (collar (-2)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h1 : Continuous fun p : ↥(collar (-2)) =>
      (fibreNormFun (-2) (p : Vk (-2)) - 1 / 2)⁻¹ := by
    refine Continuous.inv₀ ?_ (fun p => ?_)
    · exact ((continuous_fibreNormFun (-2)).comp continuous_subtype_val).sub continuous_const
    · have hp := mem_collar.mp p.2
      intro h0
      linarith [show fibreNormFun (-2) (p : Vk (-2)) - 1 / 2 = 0 from h0]
  have h2 : Continuous fun p : ↥(collar (-2)) =>
      (e (collarPsi (-2) p) : EuclideanSpace ℝ (Fin 8)) :=
    continuous_subtype_val.comp (e.contMDiff.continuous.comp (collarPsi (-2)).continuous)
  exact (h1.smul h2).congr (fun p => (capFunK_of_mem e p.2).symm)

/-- The direction map `z ↦ z/‖z‖`, as a continuous map on the punctured space. -/
theorem continuous_unitOf_punct :
    Continuous (fun w : ↥capPunct => unitOf (w : EuclideanSpace ℝ (Fin 8))) := by
  have h1 : Continuous fun w : ↥capPunct => (‖(w : EuclideanSpace ℝ (Fin 8))‖)⁻¹ :=
    (continuous_norm.comp continuous_subtype_val).inv₀
      (fun w => norm_ne_zero_iff.mpr (ne_zero_of_mem_capPunct w.2))
  have h2 : Continuous fun w : ↥capPunct => (w : EuclideanSpace ℝ (Fin 8)) :=
    continuous_subtype_val
  have hcoe : Continuous fun w : ↥capPunct =>
      ((unitOf (w : EuclideanSpace ℝ (Fin 8)) : Sph8) : EuclideanSpace ℝ (Fin 8)) :=
    (h1.smul h2).congr (fun w => (coe_unitOf_of_ne (ne_zero_of_mem_capPunct w.2)).symm)
  exact (hcoe.subtype_mk (fun w => (unitOf (w : EuclideanSpace ℝ (Fin 8))).2)).congr
    (fun w => Subtype.ext rfl)

theorem continuousOn_capFunInvK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    ContinuousOn (capFunInvK e) capPunct := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h1 : Continuous fun w : ↥capPunct => ‖(w : EuclideanSpace ℝ (Fin 8))‖⁻¹ + 1 / 2 :=
    ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun w => norm_ne_zero_iff.mpr (ne_zero_of_mem_capPunct w.2))).add continuous_const
  have h2 : Continuous fun w : ↥capPunct =>
      mkToVkFun (-2) (e.symm (unitOf (w : EuclideanSpace ℝ (Fin 8)))) :=
    (continuous_mkToVkFun (-2)).comp (e.symm.contMDiff.continuous.comp continuous_unitOf_punct)
  exact ((continuous_vScale_uncurry (-2)).comp (h1.prodMk h2)).congr
    (fun w => (capFunInvK_of_ne e (ne_zero_of_mem_capPunct w.2)).symm)

/-! ## The gluing homeomorphism -/

/-- **The compact capping map as an open partial homeomorphism** `Vk (-2) ⇢ ℝ⁸`, from the collar
`{1/2 < ν}` onto the punctured space `ℝ⁸ ∖ {0}`. -/
def capPhiK (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    OpenPartialHomeomorph (Vk (-2)) (EuclideanSpace ℝ (Fin 8)) where
  toFun := capFunK e
  invFun := capFunInvK e
  source := collar (-2)
  target := capPunct
  map_source' := fun p hp => capFunK_mem e hp
  map_target' := fun z hz => capFunInvK_mem e hz
  left_inv' := fun p hp => capFunInvK_capFunK e hp
  right_inv' := fun z hz => capFunK_capFunInvK e hz
  continuousOn_toFun := continuousOn_capFunK e
  continuousOn_invFun := continuousOn_capFunInvK e
  open_source := isOpen_collar (-2)
  open_target := isOpen_capPunct

/-! ## The datum predicate -/

/-- A gluing datum on the pair `(Vk (-2), ℝ⁸)` is **the compact capping** associated to the
diffeomorphism `e : Mk (-2) ≃ S⁷` if its open sets are the collar `{1/2 < ν}` and the punctured
space `ℝ⁸ ∖ {0}`, and its gluing map is `capFunK e`.  The glued space is then the closed
`8`-manifold `X = D(ξ) ∪_e D⁸`. -/
def IsCompactCapping (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (D : CapData) : Prop :=
  D.U = collar (-2) ∧ D.V = capPunct ∧
    ∀ p : ↥D.U, (D.φ (p : Vk (-2)) : EuclideanSpace ℝ (Fin 8)) = capFunK e (p : Vk (-2))

/-! ## The chartwise formulas -/

/-- **The first chart of the compact capping map.** -/
theorem capFunK_ιX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFunK e ((vData (-2)).ιX a) =
      (‖a.2‖ - 1 / 2)⁻¹ •
        (e ((clutchData (-2)).ιX (a.1, qDir a.2)) : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : (vData (-2)).ιX a ∈ collar (-2) :=
    mem_collar.mpr (by rw [fibreNormFun_ιX]; exact ha)
  rw [capFunK_of_mem e hmem, fibreNormFun_ιX, collarPsi_ιX a ha]

/-- **The second chart of the compact capping map.** -/
theorem capFunK_ιY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFunK e ((vData (-2)).ιY a) =
      (‖a.2‖ - 1 / 2)⁻¹ •
        (e ((clutchData (-2)).ιY (a.1, qDir a.2)) : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : (vData (-2)).ιY a ∈ collar (-2) :=
    mem_collar.mpr (by rw [fibreNormFun_ιY]; exact ha)
  rw [capFunK_of_mem e hmem, fibreNormFun_ιY, collarPsi_ιY a ha]

/-- **The first chart of the inverse compact capping map.** -/
theorem capFunInvK_eq_ιX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) {p : MSpace}
    (hp : e.symm (unitOf z) = (clutchData (-2)).ιX p) :
    capFunInvK e z = (vData (-2)).ιX (p.1, (‖z‖⁻¹ + 1 / 2) • (p.2 : Quaternion ℝ)) := by
  rw [capFunInvK_of_ne e hz, hp, mkToVk_ιX, vScale_ιX]

/-- **The second chart of the inverse compact capping map.** -/
theorem capFunInvK_eq_ιY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {z : EuclideanSpace ℝ (Fin 8)} (hz : z ≠ 0) {p : MSpace}
    (hp : e.symm (unitOf z) = (clutchData (-2)).ιY p) :
    capFunInvK e z = (vData (-2)).ιY (p.1, (‖z‖⁻¹ + 1 / 2) • (p.2 : Quaternion ℝ)) := by
  rw [capFunInvK_of_ne e hz, hp, mkToVk_ιY, vScale_ιY]

/-! ## The chartwise formulas as functions -/

/-- The explicit first-chart formula for the compact capping map. -/
def chartFormKX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) : MSpace8 :=
  (‖a.2‖ - 1 / 2)⁻¹ • (vkModelIso.symm
    ((e ((clutchData (-2)).ιX (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))

/-- The explicit second-chart formula for the compact capping map. -/
def chartFormKY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) : MSpace8 :=
  (‖a.2‖ - 1 / 2)⁻¹ • (vkModelIso.symm
    ((e ((clutchData (-2)).ιY (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))

/-- The explicit first-chart formula for the inverse compact capping map. -/
def chartInvFormKX (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (w : MSpace8) : MSpace8 :=
  (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).1,
    (‖vkModelIso w‖⁻¹ + 1 / 2) • ((((clutchData (-2)).homX.symm
      (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ))

/-- The explicit second-chart formula for the inverse compact capping map. -/
def chartInvFormKY (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (w : MSpace8) : MSpace8 :=
  (((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).1,
    (‖vkModelIso w‖⁻¹ + 1 / 2) • ((((clutchData (-2)).homY.symm
      (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ))

/-- The compact capping map on the first chart is `vkModelIso` of the explicit first-chart
formula. -/
theorem capFunK_ιX' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFunK e ((vData (-2)).ιX a) = vkModelIso (chartFormKX e a) := by
  rw [capFunK_ιX e a ha, chartFormKX, map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- The compact capping map on the second chart is `vkModelIso` of the explicit second-chart
formula. -/
theorem capFunK_ιY' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    (a : MSpace8) (ha : 1 / 2 < ‖a.2‖) :
    capFunK e ((vData (-2)).ιY a) = vkModelIso (chartFormKY e a) := by
  rw [capFunK_ιY e a ha, chartFormKY, map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse compact capping map on the first chart is `ιX` of the explicit first-chart
formula. -/
theorem capFunInvK_eq_ιX' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {w : MSpace8} (hz : vkModelIso w ≠ 0)
    (hw : e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX) :
    capFunInvK e (vkModelIso w) = (vData (-2)).ιX (chartInvFormKX e w) := by
  obtain ⟨p, hp⟩ := hw
  have hpair : ((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))) = p := by
    rw [← hp]
    exact (clutchData (-2)).homX_symm_apply p
  rw [capFunInvK_eq_ιX e hz hp.symm]
  have hval : chartInvFormKX e w
      = (p.1, (‖vkModelIso w‖⁻¹ + 1 / 2) • ((p.2 : QS3) : Quaternion ℝ)) := by
    rw [chartInvFormKX, hpair]
  rw [hval]

/-- The inverse compact capping map on the second chart is `ιY` of the explicit second-chart
formula. -/
theorem capFunInvK_eq_ιY' (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8)
    {w : MSpace8} (hz : vkModelIso w ≠ 0)
    (hw : e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY) :
    capFunInvK e (vkModelIso w) = (vData (-2)).ιY (chartInvFormKY e w) := by
  obtain ⟨p, hp⟩ := hw
  have hpair : ((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))) = p := by
    rw [← hp]
    exact (clutchData (-2)).homY_symm_apply p
  rw [capFunInvK_eq_ιY e hz hp.symm]
  have hval : chartInvFormKY e w
      = (p.1, (‖vkModelIso w‖⁻¹ + 1 / 2) • ((p.2 : QS3) : Quaternion ℝ)) := by
    rw [chartInvFormKY, hpair]
  rw [hval]

end

end Work.Milnor
