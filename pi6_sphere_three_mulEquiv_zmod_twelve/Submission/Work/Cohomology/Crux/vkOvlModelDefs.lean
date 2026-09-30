import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Glue.Basic

set_option synthInstance.maxHeartbeats 400000

/-!
# The model pair `(S³ × D⁴, S³ × S³)` for the overlap of the two charts of `Vk (-2)`

This file collects the *definitions* used to prove
`Work.Cohomology.Crux.vkOvl_model_pair_map`: the comparison of the overlap
`U ∩ V` of the two charts of `Vk (-2)` (with its sphere-bundle part) with the model pair
`(PairXT, PairAT) = (S³ × D⁴, S³ × S³)`.

* `S3H = S³ × ℍ` is the "cylindrical" model of the gluing region;
* `ovlV = {p : ℝ⁴ × ℍ | p.1 ≠ 0}` is the gluing region itself, inside the first chart;
* `ovlHomeo : ↥(U ∩ V) ≃ₜ ovlV` is the chart identification;
* `PhiM : S³ × ℍ ⟶ S³ × D⁴`, `(s, y) ↦ (s, y / max 1 ‖y‖)` is the fibrewise radial retraction;
* `PsiM : S³ × D⁴ ⟶ S³ × ℍ` is its homotopy inverse (the inclusion);
* `pS : ovlV ⟶ S³ × ℍ`, `q ↦ (q.1 / ‖q.1‖, q.2)` is the radial retraction of the base and
  `pSi` is the inclusion.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology

namespace Work.Cohomology.Crux

noncomputable section

/-- The model total space `S³ × ℍ`. -/
abbrev S3H : Type := ↥Sph3T × Quaternion ℝ

/-- The sphere-bundle part `S³ × S³` of `S³ × ℍ`. -/
abbrev S3HA : Set S3H := {p | ‖p.2‖ = 1}

/-- The gluing region `{x ≠ 0} × ℍ` of the two charts of `Vk (-2)`, as a topological space. -/
abbrev ovlV : Type := {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}

/-- The sphere-bundle part of the gluing region: the fibre coordinate has norm one. -/
abbrev ovlVA : Set ovlV := {q | ‖(q : Submission.Milnor.MSpace8).2‖ = 1}

/-- The linear isometry `ℍ ≅ ℝ⁴` identifying the quaternion fibre with the disc `D⁴ ⊆ ℝ⁴`. -/
def linIsom : Quaternion ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  Quaternion.linearIsometryEquivTuple

/-- The radial shrinking factor `ρ(y) = (max 1 ‖y‖)⁻¹`. -/
def rho (y : Quaternion ℝ) : ℝ := (max 1 ‖linIsom y‖)⁻¹

/-- The radial retraction of `ℍ ≅ ℝ⁴` onto the closed unit ball. -/
def fibRetract (y : Quaternion ℝ) : EuclideanSpace ℝ (Fin 4) := rho y • linIsom y

theorem rho_pos (y : Quaternion ℝ) : 0 < rho y :=
  inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem rho_nonneg (y : Quaternion ℝ) : 0 ≤ rho y := le_of_lt (rho_pos y)

theorem rho_mul_max_eq_one (y : Quaternion ℝ) : rho y * max 1 ‖linIsom y‖ = 1 :=
  inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem norm_fibRetract_le_one (y : Quaternion ℝ) : ‖fibRetract y‖ ≤ 1 := by
  rw [fibRetract, norm_smul, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg y)]
  calc rho y * ‖linIsom y‖ ≤ rho y * max 1 ‖linIsom y‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (rho_nonneg y)
    _ = 1 := rho_mul_max_eq_one y

theorem fibRetract_mem (y : Quaternion ℝ) :
    fibRetract y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact norm_fibRetract_le_one y)

/-- On the unit sphere of `ℍ` the retraction is the linear isometry itself. -/
theorem fibRetract_of_norm_eq_one {y : Quaternion ℝ} (hy : ‖y‖ = 1) :
    fibRetract y = linIsom y := by
  rw [fibRetract, rho, linIsom.norm_map, hy, max_eq_left le_rfl, inv_one, one_smul]

/-- On the closed unit ball of `ℍ` the retraction is the identity (in `ℝ⁴` coordinates). -/
theorem fibRetract_of_norm_le_one {y : Quaternion ℝ} (hy : ‖y‖ ≤ 1) :
    fibRetract y = linIsom y := by
  rw [fibRetract, rho, linIsom.norm_map, max_eq_left hy, inv_one, one_smul]

theorem rho_of_norm_le_one {y : Quaternion ℝ} (hy : ‖y‖ ≤ 1) : rho y = 1 := by
  rw [rho, linIsom.norm_map, max_eq_left hy, inv_one]

theorem linIsom_smul (c : ℝ) (y : Quaternion ℝ) : linIsom (c • y) = c • linIsom y :=
  map_smul linIsom c y

theorem continuous_linIsom : Continuous linIsom := linIsom.continuous

theorem continuous_linIsom_symm : Continuous linIsom.symm := linIsom.symm.continuous

theorem continuous_rho : Continuous rho := by
  rw [show rho = fun y : Quaternion ℝ => (max 1 ‖linIsom y‖)⁻¹ from rfl]
  exact ((continuous_const.max continuous_linIsom.norm).inv₀
    (fun y => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))))

theorem continuous_fibRetract : Continuous fibRetract := by
  rw [show fibRetract = fun y : Quaternion ℝ => rho y • linIsom y from rfl]
  exact continuous_rho.smul continuous_linIsom

/-! ## The map `Φ : S³ × ℍ ⟶ S³ × D⁴` and its homotopy inverse `Ψ` -/

/-- The fibrewise radial retraction `(s, y) ↦ (s, y/max 1 ‖y‖)`. -/
def PhiM : C(S3H, PairXT) where
  toFun p := (p.1, ⟨fibRetract p.2, fibRetract_mem p.2⟩)
  continuous_toFun := Continuous.prodMk continuous_fst
    ((continuous_fibRetract.comp continuous_snd).subtype_mk (fun p => fibRetract_mem p.2))

/-- The inclusion `(s, z) ↦ (s, z)` of the disc bundle into `S³ × ℍ`. -/
def PsiM : C(PairXT, S3H) where
  toFun p := (p.1, linIsom.symm (p.2 : EuclideanSpace ℝ (Fin 4)))
  continuous_toFun := Continuous.prodMk continuous_fst
    (continuous_linIsom_symm.comp (continuous_subtype_val.comp continuous_snd))

@[simp] theorem PhiM_apply (p : S3H) :
    PhiM p = ((p.1, ⟨fibRetract p.2, fibRetract_mem p.2⟩) : ↥PairXT) := rfl

@[simp] theorem PsiM_apply (p : ↥PairXT) :
    PsiM p = (p.1, linIsom.symm (p.2 : EuclideanSpace ℝ (Fin 4))) := rfl

/-- The retraction is a section of the inclusion: `Φ ∘ Ψ = id`. -/
theorem PhiM_comp_PsiM : PhiM.comp PsiM = ContinuousMap.id ↥PairXT := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have hle : ‖linIsom.symm (p.2 : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      simpa [dist_zero_right] using Metric.mem_closedBall.mp p.2.2
    show fibRetract (linIsom.symm (p.2 : EuclideanSpace ℝ (Fin 4))) =
      (p.2 : EuclideanSpace ℝ (Fin 4))
    rw [fibRetract, linIsom.apply_symm_apply, rho_of_norm_le_one hle, one_smul]

/-- `Φ` maps the sphere bundle `S³ × S³` into `S³ × S³`. -/
theorem PhiM_mem_PairAT {p : S3H} (hp : p ∈ S3HA) : PhiM p ∈ PairAT := by
  have hp' : ‖p.2‖ = 1 := hp
  show (fibRetract p.2 : EuclideanSpace ℝ (Fin 4)) ∈
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  rw [Metric.mem_sphere, dist_zero_right, fibRetract_of_norm_eq_one hp', linIsom.norm_map, hp']

/-- `Ψ` maps the sphere bundle `S³ × S³` back into `S³ × S³`. -/
theorem PsiM_mem_S3HA {p : ↥PairXT} (hp : p ∈ PairAT) : PsiM p ∈ S3HA := by
  have hp' : (p.2 : EuclideanSpace ℝ (Fin 4)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    hp
  rw [Metric.mem_sphere, dist_zero_right] at hp'
  change ‖linIsom.symm (p.2 : EuclideanSpace ℝ (Fin 4))‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  exact hp'

/-! ## The map `pS : {x ≠ 0} × ℍ ⟶ S³ × ℍ` and its homotopy inverse `pSi` -/

/-- Radial retraction of the base: `(x, y) ↦ (x/‖x‖, y)`. -/
def pS : C(ovlV, S3H) :=
  Work.Milnor.vSphProj.prodMk
    ⟨fun q => (q : Submission.Milnor.MSpace8).2, continuous_subtype_val.snd⟩

theorem pSi_mem (p : S3H) :
    (((p.1 : EuclideanSpace ℝ (Fin 4)), p.2) : Submission.Milnor.MSpace8) ∈
      Submission.Milnor.vOpens := by
  rw [Submission.Milnor.mem_vOpens]
  show (p.1 : EuclideanSpace ℝ (Fin 4)) ≠ 0
  intro h
  have h1 : ‖(p.1 : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    simp at *
  rw [h, norm_zero] at h1
  norm_num at h1

/-- The inclusion `(s, y) ↦ (s, y)` of `S³ × ℍ` into the gluing region `{x ≠ 0} × ℍ`. -/
def pSi : C(S3H, ovlV) where
  toFun p := ⟨(((p.1 : EuclideanSpace ℝ (Fin 4)), p.2) : Submission.Milnor.MSpace8), pSi_mem p⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd) pSi_mem

theorem vSphProj_apply (q : ovlV) :
    (Work.Milnor.vSphProj q : EuclideanSpace ℝ (Fin 4)) =
      (‖(q : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ • (q : Submission.Milnor.MSpace8).1 := rfl

@[simp] theorem pS_apply (q : ovlV) :
    pS q = (Work.Milnor.vSphProj q, (q : Submission.Milnor.MSpace8).2) := rfl

@[simp] theorem pSi_apply (p : S3H) :
    (pSi p : Submission.Milnor.MSpace8) = ((p.1 : EuclideanSpace ℝ (Fin 4)), p.2) := rfl

/-- `pS` is a retraction of the inclusion `pSi`: `pS ∘ pSi = id`. -/
theorem pS_comp_pSi : pS.comp pSi = ContinuousMap.id S3H := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · show Work.Milnor.vSphProj (pSi p) = p.1
    apply Subtype.ext
    rw [vSphProj_apply, pSi_apply]
    have h : ‖(p.1 : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      simp at *
    rw [h, inv_one, one_smul]
  · rfl

/-- `pS` maps the sphere-bundle part into the sphere-bundle part. -/
theorem pS_mem_S3HA {q : ovlV} (hq : q ∈ ovlVA) : pS q ∈ S3HA := hq

/-- `pSi` maps the sphere-bundle part back into the sphere-bundle part. -/
theorem pSi_mem_ovlVA {p : S3H} (hp : p ∈ S3HA) : pSi p ∈ ovlVA := hp

/-! ## The chart identification `U ∩ V ≃ {x ≠ 0} × ℍ` -/

/-- The chart coordinates of a point of the overlap lie in the gluing region. -/
theorem ovlHomeo_toFun_mem (z : ↥(vkU ∩ vkV)) :
    (Submission.Milnor.vData (-2)).homX.symm (z : vkPairX) ∈ Submission.Milnor.vOpens := by
  have hz : (z : vkPairX) ∈
      (Submission.Milnor.vData (-2)).ιX '' (Submission.Milnor.vData (-2)).U := by
    rw [Work.Milnor.image_U_eq_inter_range (-2)]
    exact z.2
  obtain ⟨p, hpU, hpz⟩ := hz
  rw [show (z : vkPairX) = (Submission.Milnor.vData (-2)).ιX p from hpz.symm,
    (Submission.Milnor.vData (-2)).homX_symm_apply p]
  exact hpU

/-- A point of the gluing region lies in both charts. -/
theorem ovlHomeo_invFun_mem (q : ovlV) :
    ((Submission.Milnor.vData (-2)).ιX (q : Submission.Milnor.MSpace8) : vkPairX) ∈ vkU ∩ vkV :=
  ⟨⟨(q : Submission.Milnor.MSpace8), rfl⟩,
    ⟨(Submission.Milnor.vData (-2)).φ (q : Submission.Milnor.MSpace8),
      ((Submission.Milnor.vData (-2)).ιX_eq_ιY_iff.mpr ⟨q.2, rfl⟩).symm⟩⟩

/-- The chart identification of the overlap `U ∩ V` of the two charts of `Vk (-2)` with the
gluing region `{x ≠ 0} × ℍ` in the first chart. -/
def ovlHomeo : ↥(vkU ∩ vkV) ≃ₜ ovlV where
  toFun z := ⟨(Submission.Milnor.vData (-2)).homX.symm (z : vkPairX), ovlHomeo_toFun_mem z⟩
  invFun q := ⟨((Submission.Milnor.vData (-2)).ιX (q : Submission.Milnor.MSpace8) : vkPairX),
    ovlHomeo_invFun_mem q⟩
  left_inv z := by
    have hz : (z : vkPairX) ∈ (Submission.Milnor.vData (-2)).homX.target := by
      rw [(Submission.Milnor.vData (-2)).homX_target]
      exact z.2.1
    refine Subtype.ext ?_
    show (Submission.Milnor.vData (-2)).ιX
      ((Submission.Milnor.vData (-2)).homX.symm (z : vkPairX)) = (z : vkPairX)
    rw [← (Submission.Milnor.vData (-2)).homX_apply
      ((Submission.Milnor.vData (-2)).homX.symm (z : vkPairX))]
    exact (Submission.Milnor.vData (-2)).homX.right_inv hz
  right_inv q := by
    refine Subtype.ext ?_
    show (Submission.Milnor.vData (-2)).homX.symm
      ((Submission.Milnor.vData (-2)).ιX (q : Submission.Milnor.MSpace8)) =
      (q : Submission.Milnor.MSpace8)
    exact (Submission.Milnor.vData (-2)).homX_symm_apply (q : Submission.Milnor.MSpace8)
  continuous_toFun := by
    have h1 : Continuous (fun z : ↥(vkU ∩ vkV) => (z : vkPairX)) := continuous_subtype_val
    have h2 : Continuous (fun z : ↥(vkU ∩ vkV) =>
        (Submission.Milnor.vData (-2)).homX.symm (z : vkPairX)) :=
      ((Submission.Milnor.vData (-2)).homX.continuousOn_symm).comp_continuous h1 (fun z => by
        rw [(Submission.Milnor.vData (-2)).homX_target]
        exact z.2.1)
    exact h2.subtype_mk ovlHomeo_toFun_mem
  continuous_invFun := by
    have h1 : Continuous (fun q : ovlV => ((Submission.Milnor.vData (-2)).ιX
        (q : Submission.Milnor.MSpace8) : vkPairX)) :=
      ((Submission.Milnor.vData (-2)).continuous_ιX).comp continuous_subtype_val
    exact h1.subtype_mk ovlHomeo_invFun_mem

@[simp] theorem ovlHomeo_apply_coe (z : ↥(vkU ∩ vkV)) :
    ((ovlHomeo z : ovlV) : Submission.Milnor.MSpace8) =
      (Submission.Milnor.vData (-2)).homX.symm (z : vkPairX) := rfl

@[simp] theorem ovlHomeo_symm_apply_coe (q : ovlV) :
    ((ovlHomeo.symm q : ↥(vkU ∩ vkV)) : vkPairX) =
      (Submission.Milnor.vData (-2)).ιX (q : Submission.Milnor.MSpace8) := rfl

theorem ovlHomeo_ιX (z : ↥(vkU ∩ vkV)) :
    (Submission.Milnor.vData (-2)).ιX
      ((ovlHomeo z : ovlV) : Submission.Milnor.MSpace8) = (z : vkPairX) := by
  have hz : (z : vkPairX) ∈ (Submission.Milnor.vData (-2)).homX.target := by
    rw [(Submission.Milnor.vData (-2)).homX_target]
    exact z.2.1
  show (Submission.Milnor.vData (-2)).ιX
      ((Submission.Milnor.vData (-2)).homX.symm (z : vkPairX)) = (z : vkPairX)
  rw [← (Submission.Milnor.vData (-2)).homX_apply
    ((Submission.Milnor.vData (-2)).homX.symm (z : vkPairX))]
  exact (Submission.Milnor.vData (-2)).homX.right_inv hz

/-- The sphere-bundle part of the overlap is exactly the set of points whose fibre coordinate
(in the first chart) has norm one. -/
theorem mem_vkOvlA_iff (z : ↥(vkU ∩ vkV)) :
    (z : vkPairX) ∈ vkPairA ↔ (ovlHomeo z : ovlV) ∈ ovlVA := by
  rw [← ovlHomeo_ιX z]
  change ((Submission.Milnor.vData (-2)).ιX
      ((ovlHomeo z : ovlV) : Submission.Milnor.MSpace8)) ∈ Set.range (Work.Milnor.mkToVkFun (-2))
    ↔ ‖((ovlHomeo z : ovlV) : Submission.Milnor.MSpace8).2‖ = 1
  rw [Work.Milnor.mem_range_mkToVkFun_iff, Work.Milnor.fibreNormFun_ιX]

@[simp] theorem ovlHomeo_mem_ovlVA_iff (z : ↥(vkU ∩ vkV)) :
    (ovlHomeo z : ovlV) ∈ ovlVA ↔ (z : vkPairX) ∈ vkPairA :=
  (mem_vkOvlA_iff z).symm

end

end Work.Cohomology.Crux
