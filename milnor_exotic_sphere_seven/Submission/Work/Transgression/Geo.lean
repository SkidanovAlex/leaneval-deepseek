import Mathlib
import Submission.Work.Transgression.MVDefs
import Submission.Work.Transgression.H4Vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The geometric inputs of the transgression assembly

This module proves the geometric facts consumed by `Submission/Work/Transgression/MV.lean`.
-/

namespace Work.Transgression

open Work.TangentClasses Work.Thom CategoryTheory Limits

noncomputable section

namespace Geo

/-! ## 1. The coordinates of a point of `pU` -/

/-- The coercion `↥(pU a b) → E` is continuous. -/
lemma continuous_pU_coe (a b : ℤ) :
    Continuous fun p : ↥(pU a b) => (p : (Zb a b).TotalSpace) :=
  Continuous.comp
    (continuous_subtype_val :
      Continuous (Subtype.val : ↥(Work.Thom.zeroComplement (Zb a b)) → (Zb a b).TotalSpace))
    (continuous_subtype_val :
      Continuous (Subtype.val : ↥(pU a b) → ↥(Work.Thom.zeroComplement (Zb a b))))

/-- The base of a point of the piece `pU`. -/
def uB (a b : ℤ) (p : ↥(pU a b)) : Work.Agree.S4 := ((p : (Zb a b).TotalSpace).1)

/-- The first-chart fibre coordinate of a point of the piece `pU`. -/
def uV (a b : ℤ) (p : ↥(pU a b)) : EuclideanSpace ℝ (Fin 4) :=
  (show EuclideanSpace ℝ (Fin 4) from ((p : (Zb a b).TotalSpace).2))

lemma uB_mem (a b : ℤ) (p : ↥(pU a b)) : uB a b p ∈ Work.Agree.hemi0 := p.2

lemma chart0_eq_uV (a b : ℤ) (p : ↥(pU a b)) :
    chart0 a b (p : (Zb a b).TotalSpace) = uV a b p :=
  chart0_of_mem a b p.2

lemma uV_ne_zero (a b : ℤ) (p : ↥(pU a b)) : uV a b p ≠ 0 := by
  intro h
  have h1 : fibreNorm (Zb a b) ((p : (Zb a b).TotalSpace)) = 0 := by
    rw [show fibreNorm (Zb a b) ((p : (Zb a b).TotalSpace)) = ‖uV a b p‖ from rfl, h, norm_zero]
  exact (SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mp p.1.2 h1

lemma continuous_uB (a b : ℤ) : Continuous fun p : ↥(pU a b) => uB a b p :=
  ((Zb a b).continuous_proj).comp (continuous_pU_coe a b)

lemma continuous_chart0_pU' (a b : ℤ) :
    Continuous fun p : ↥(pU a b) => chart0 a b (p : (Zb a b).TotalSpace) :=
  (continuousOn_chart0 a b).comp_continuous (continuous_pU_coe a b) (fun p => p.2)

/-! ## 2. Continuity of a pair with base in the first chart -/

/-- **A pair with base in `hemi0` is a continuous section.** -/
theorem continuous_mk_hemi0 (a b : ℤ) {X : Type} [TopologicalSpace X]
    (bb : C(X, Work.Agree.S4)) (hb : ∀ x, bb x ∈ Work.Agree.hemi0)
    (g : C(X, EuclideanSpace ℝ (Fin 4))) :
    Continuous (fun x => (⟨bb x, g x⟩ : (Zb a b).TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsrc : (⟨bb x₀, g x₀⟩ : (Zb a b).TotalSpace) ∈ ((Zb a b).localTriv false).source := by
    rw [VectorBundleCore.mem_localTriv_source]
    exact hb x₀
  have hev : (fun x => ((Zb a b).localTriv false) (⟨bb x, g x⟩ : (Zb a b).TotalSpace))
      = fun x => (bb x, g x) := by
    funext x
    rw [VectorBundleCore.localTriv_apply]
    have hidx : (Zb a b).indexAt (bb x) = false := if_neg (hb x)
    rw [hidx]
    rfl
  refine ((Zb a b).localTriv false).continuousAt_of_comp_left ?_ hsrc ?_
  · show ContinuousAt (fun x => (Zb a b).proj (⟨bb x, g x⟩ : (Zb a b).TotalSpace)) x₀
    rw [show (fun x => (Zb a b).proj (⟨bb x, g x⟩ : (Zb a b).TotalSpace)) = fun x => bb x
      from by funext x; rfl]
    exact bb.continuous.continuousAt
  · show ContinuousAt (fun x => ((Zb a b).localTriv false)
      (⟨bb x, g x⟩ : (Zb a b).TotalSpace)) x₀
    rw [hev]
    exact (bb.continuous.continuousAt.prodMk g.continuous.continuousAt)

/-- Two points of the total space are equal as soon as their bases and their first-chart fibre
coordinates agree. -/
lemma totalSpace_ext (a b : ℤ) {x y : (Zb a b).TotalSpace} (hb : x.1 = y.1)
    (hf : (show EuclideanSpace ℝ (Fin 4) from x.2) =
      (show EuclideanSpace ℝ (Fin 4) from y.2)) : x = y := by
  apply Bundle.TotalSpace.ext hb
  rw [show x.2 = (show EuclideanSpace ℝ (Fin 4) from x.2) from rfl,
    show y.2 = (show EuclideanSpace ℝ (Fin 4) from y.2) from rfl, hf]

/-! ## 3. The section of `rhoU` and its homotopy -/

/-- **The section of `rhoU` over the base point `↑0`.** -/
def sU (a b : ℤ) : C(MV.S3Q, ↥(pU a b)) where
  toFun v :=
    ⟨⟨⟨(↑(0 : EuclideanSpace ℝ (Fin 4)) : Work.Agree.S4),
        Work.Agree.ofQ (v : Quaternion ℝ)⟩,
      fun h => ofQ_ne_zero v (by simpa using h)⟩,
     OnePoint.coe_ne_infty (0 : EuclideanSpace ℝ (Fin 4))⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk
        (Geo.continuous_mk_hemi0 a b (ContinuousMap.const MV.S3Q (↑(0 : EuclideanSpace ℝ (Fin 4))))
          (fun v => OnePoint.coe_ne_infty _)
          ⟨fun v => Work.Agree.ofQ (v : Quaternion ℝ),
            Work.Agree.ofQ.continuous.comp continuous_subtype_val⟩)
        (fun v => fun h => ofQ_ne_zero v (by simpa using h)))
      (fun v => OnePoint.coe_ne_infty _)

/-- The base path of the deformation of `pU` onto its section. -/
def uBaseH (a b : ℤ) (x : unitInterval × ↥(pU a b)) : Work.Agree.S4 :=
  ↑((1 - (x.1 : ℝ)) • Work.Agree.coord0 (uB a b x.2))

/-- The fibre path of the deformation of `pU`. -/
def uFibH (a b : ℤ) (x : unitInterval × ↥(pU a b)) : EuclideanSpace ℝ (Fin 4) :=
  ((1 - (x.1 : ℝ)) + (x.1 : ℝ) *
    (‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹) •
      chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)

/-- The coefficient of the fibre rescaling is positive. -/
lemma uCoef_pos (a b : ℤ) (x : unitInterval × ↥(pU a b)) :
    0 < (1 - (x.1 : ℝ)) + (x.1 : ℝ) *
      (‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹ := by
  have hv : 0 < ‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖ :=
    norm_pos_iff.mpr (chart0_ne_zero a b _ x.2.2)
  rcases eq_or_lt_of_le x.1.2.2 with h | h
  · rw [h, sub_self, zero_add, one_mul]
    exact inv_pos.mpr hv
  · have h2 : 0 < 1 - (x.1 : ℝ) := by linarith
    have h4 : 0 ≤ (x.1 : ℝ) * (‖chart0 a b
        ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹ :=
      mul_nonneg x.1.2.1 (le_of_lt (inv_pos.mpr hv))
    linarith

/-- The point of `pU` at time `t` of the deformation. -/
def uHom (a b : ℤ) (x : unitInterval × ↥(pU a b)) : ↥(pU a b) :=
  ⟨⟨⟨uBaseH a b x, uFibH a b x⟩,
    fun h => by
      have h' : uFibH a b x = 0 := h
      rcases smul_eq_zero.mp (show ((1 - (x.1 : ℝ)) + (x.1 : ℝ) *
          (‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹) •
          chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace) = 0 from h') with h2 | h2
      · exact absurd h2 (ne_of_gt (uCoef_pos a b x))
      · exact absurd h2 (chart0_ne_zero a b _ x.2.2)⟩,
   OnePoint.coe_ne_infty _⟩

lemma continuous_uBaseH (a b : ℤ) : Continuous (uBaseH a b) := by
  refine OnePoint.continuous_coe.comp ?_
  refine ((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul ?_
  refine Work.Agree.continuousOn_coord0.comp_continuous ?_ (fun x => uB_mem a b x.2)
  exact (continuous_uB a b).comp continuous_snd

lemma continuous_uFibH (a b : ℤ) : Continuous (uFibH a b) := by
  have hchart : Continuous fun x : unitInterval × ↥(pU a b) =>
      chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace) :=
    (continuous_chart0_pU' a b).comp continuous_snd
  have hc : Continuous fun x : unitInterval × ↥(pU a b) =>
      (1 - (x.1 : ℝ)) + (x.1 : ℝ) *
        (‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹ :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((hchart.norm).inv₀ (fun x => norm_ne_zero_iff.mpr (chart0_ne_zero a b _ x.2.2))))
  exact hc.smul hchart

theorem continuous_uHom (a b : ℤ) : Continuous (uHom a b) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk
      (Geo.continuous_mk_hemi0 a b
        ⟨uBaseH a b, continuous_uBaseH a b⟩ (fun x => OnePoint.coe_ne_infty _)
        ⟨uFibH a b, continuous_uFibH a b⟩)
      (fun x => fun h => by
        have h' : uFibH a b x = 0 := h
        rcases smul_eq_zero.mp (show ((1 - (x.1 : ℝ)) + (x.1 : ℝ) *
            (‖chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace)‖)⁻¹) •
            chart0 a b ((x.2 : ↥(pU a b)) : (Zb a b).TotalSpace) = 0 from h') with h2 | h2
        · exact absurd h2 (ne_of_gt (uCoef_pos a b x))
        · exact absurd h2 (chart0_ne_zero a b _ x.2.2)))
    (fun x => OnePoint.coe_ne_infty _)

theorem uHom_zero (a b : ℤ) (p : ↥(pU a b)) : uHom a b (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  refine Geo.totalSpace_ext a b ?_ ?_
  · show (↑(((1 : ℝ) - 0) • Work.Agree.coord0 (uB a b p)) : Work.Agree.S4) = uB a b p
    rw [sub_zero, one_smul, Work.Agree.coord0_mem (uB_mem a b p)]
  · show ((1 : ℝ) - 0 + 0 * (‖chart0 a b (p : (Zb a b).TotalSpace)‖)⁻¹) •
        chart0 a b (p : (Zb a b).TotalSpace) =
      (show EuclideanSpace ℝ (Fin 4) from (p : (Zb a b).TotalSpace).2)
    rw [sub_zero, zero_mul, add_zero, one_smul, chart0_of_mem a b (uB_mem a b p)]

theorem uHom_one (a b : ℤ) (p : ↥(pU a b)) : uHom a b (1, p) = sU a b (rhoU a b p) := by
  apply Subtype.ext
  apply Subtype.ext
  refine Geo.totalSpace_ext a b ?_ ?_
  · show (↑(((1 : ℝ) - 1) • Work.Agree.coord0 (uB a b p)) : Work.Agree.S4) =
      (↑(0 : EuclideanSpace ℝ (Fin 4)) : Work.Agree.S4)
    rw [sub_self, zero_smul]
  · show ((1 : ℝ) - 1 + 1 * (‖chart0 a b (p : (Zb a b).TotalSpace)‖)⁻¹) •
        chart0 a b (p : (Zb a b).TotalSpace) =
      Work.Agree.ofQ ((rhoU a b p : MV.S3Q) : Quaternion ℝ)
    rw [sub_self, zero_add, one_mul]
    rw [show ((rhoU a b p : MV.S3Q) : Quaternion ℝ) =
      Work.Agree.toQ (nrmlz (chart0 a b (p : (Zb a b).TotalSpace))) from rfl,
      Work.Agree.ofQ_toQ]
    rfl

/-- **The deformation retraction of `pU` onto its section.** -/
def uHomotopy (a b : ℤ) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(pU a b)) ((sU a b).comp (rhoU a b)) :=
  ContinuousMap.Homotopy.mk ⟨uHom a b, continuous_uHom a b⟩ (uHom_zero a b) (uHom_one a b)

/-- **The pullback of `rhoU` is onto**. -/
theorem surjective_HMap_rhoU (a b : ℤ) (n : ℕ) :
    Function.Surjective (HMap (rhoU a b) n).hom := by
  have hcomp : (HMap (rhoU a b) n).hom.comp (HMap (sU a b) n).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (HMap_comp (rhoU a b) (sU a b) n)
    rw [ModuleCat.hom_comp] at h
    rw [← h, HMap_homotopic ⟨(uHomotopy a b).symm⟩ n, HMap_id, ModuleCat.hom_id]
  intro y
  exact ⟨(HMap (sU a b) n).hom y, by
    have := LinearMap.congr_fun hcomp y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this⟩

/-! ## 4. The compatibility of `rhoU` with the inclusion of the overlap -/

theorem rhoU_iotaU (a b : ℤ) :
    (rhoU a b).comp (MV.iotaU a b) = (prjB).comp (rhoW a b) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

/-! ## 5. The section of `rhoW` and the deformation onto it -/

/-- The base of a point of the overlap `pW`. -/
def wB (a b : ℤ) (p : ↥(pW a b)) : Work.Agree.S4 := ((p : (Zb a b).TotalSpace).1)

/-- The first-chart fibre coordinate of a point of the overlap `pW`. -/
def wV (a b : ℤ) (p : ↥(pW a b)) : EuclideanSpace ℝ (Fin 4) :=
  (show EuclideanSpace ℝ (Fin 4) from ((p : (Zb a b).TotalSpace).2))

lemma wB_mem0 (a b : ℤ) (p : ↥(pW a b)) : wB a b p ∈ Work.Agree.hemi0 := p.2.1

lemma wB_mem1 (a b : ℤ) (p : ↥(pW a b)) : wB a b p ∈ Work.Agree.hemi1 := p.2.2

lemma wV_ne_zero (a b : ℤ) (p : ↥(pW a b)) : wV a b p ≠ 0 := by
  intro h
  have h1 : fibreNorm (Zb a b) ((p : (Zb a b).TotalSpace)) = 0 := by
    rw [show fibreNorm (Zb a b) ((p : (Zb a b).TotalSpace)) = ‖wV a b p‖ from rfl, h, norm_zero]
  exact (SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mp p.1.2 h1

lemma coord0_wB_ne_zero (a b : ℤ) (p : ↥(pW a b)) : Work.Agree.coord0 (wB a b p) ≠ 0 :=
  Work.Agree.coord0_ne_zero (wB_mem0 a b p) (wB_mem1 a b p)

/-- **`sW` is a section of `rhoW`.** -/
theorem rhoW_sW (a b : ℤ) : (rhoW a b).comp (sW a b) = ContinuousMap.id MV.S3Q2 := by
  apply ContinuousMap.ext
  intro q
  apply Prod.ext
  · apply Subtype.ext
    show Work.Agree.toQ (dir0 (((sW a b q : ↥(pW a b)) : (Zb a b).TotalSpace).1)) =
      (q.1 : Quaternion ℝ)
    rw [show ((sW a b q : ↥(pW a b)) : (Zb a b).TotalSpace).1 =
      (↑(Work.Agree.ofQ (q.1 : Quaternion ℝ)) : Work.Agree.S4) from rfl]
    rw [dir0, Work.Agree.coord0_some]
    have hnorm : ‖Work.Agree.ofQ (q.1 : Quaternion ℝ)‖ = 1 := by
      show ‖Quaternion.linearIsometryEquivTuple (q.1 : Quaternion ℝ)‖ = 1
      rw [Quaternion.linearIsometryEquivTuple.norm_map]
      exact Submission.Milnor.norm_coe q.1
    rw [nrmlz_of_norm_eq_one hnorm, Work.Agree.toQ_ofQ]
  · apply Subtype.ext
    show Work.Agree.toQ (nrmlz (chart0 a b ((sW a b q : ↥(pW a b)) : (Zb a b).TotalSpace))) =
      (q.2 : Quaternion ℝ)
    rw [chart0_of_mem a b (show (((sW a b q : ↥(pW a b)) : (Zb a b).TotalSpace).1) ∈
      Work.Agree.hemi0 from OnePoint.coe_ne_infty _)]
    rw [show ((sW a b q : ↥(pW a b)) : (Zb a b).TotalSpace).2 =
      Work.Agree.ofQ (q.2 : Quaternion ℝ) from
      localTriv_false_symm a b (OnePoint.coe_ne_infty _) (Work.Agree.ofQ (q.2 : Quaternion ℝ))]
    have hnorm : ‖Work.Agree.ofQ (q.2 : Quaternion ℝ)‖ = 1 := by
      show ‖Quaternion.linearIsometryEquivTuple (q.2 : Quaternion ℝ)‖ = 1
      rw [Quaternion.linearIsometryEquivTuple.norm_map]
      exact Submission.Milnor.norm_coe q.2
    rw [nrmlz_of_norm_eq_one hnorm, Work.Agree.toQ_ofQ]

/-- The base path of the deformation of `pW` onto the image of its section: the first-chart
coordinate is rescaled radially towards its normalisation. -/
def wBaseH (a b : ℤ) (x : unitInterval × ↥(pW a b)) : Work.Agree.S4 :=
  ↑(((1 - (x.1 : ℝ)) + (x.1 : ℝ) * (‖Work.Agree.coord0 (wB a b x.2)‖)⁻¹) •
    Work.Agree.coord0 (wB a b x.2))

/-- The fibre path of the deformation of `pW`. -/
def wFibH (a b : ℤ) (x : unitInterval × ↥(pW a b)) : EuclideanSpace ℝ (Fin 4) :=
  ((1 - (x.1 : ℝ)) + (x.1 : ℝ) *
    (‖chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖)⁻¹) •
      chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)

lemma wBaseCoef_pos (a b : ℤ) (x : unitInterval × ↥(pW a b)) :
    0 < (1 - (x.1 : ℝ)) + (x.1 : ℝ) * (‖Work.Agree.coord0 (wB a b x.2)‖)⁻¹ := by
  have hv : 0 < ‖Work.Agree.coord0 (wB a b x.2)‖ :=
    norm_pos_iff.mpr (coord0_wB_ne_zero a b x.2)
  rcases eq_or_lt_of_le x.1.2.2 with h | h
  · rw [h, sub_self, zero_add, one_mul]
    exact inv_pos.mpr hv
  · have h2 : 0 < 1 - (x.1 : ℝ) := by linarith
    have h4 : 0 ≤ (x.1 : ℝ) * (‖Work.Agree.coord0 (wB a b x.2)‖)⁻¹ :=
      mul_nonneg x.1.2.1 (le_of_lt (inv_pos.mpr hv))
    linarith

lemma wFibCoef_pos (a b : ℤ) (x : unitInterval × ↥(pW a b)) :
    0 < (1 - (x.1 : ℝ)) + (x.1 : ℝ) *
      (‖chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖)⁻¹ := by
  have hv : 0 < ‖chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖ :=
    norm_pos_iff.mpr (chart0_ne_zero a b _ x.2.2.1)
  rcases eq_or_lt_of_le x.1.2.2 with h | h
  · rw [h, sub_self, zero_add, one_mul]
    exact inv_pos.mpr hv
  · have h2 : 0 < 1 - (x.1 : ℝ) := by linarith
    have h4 : 0 ≤ (x.1 : ℝ) * (‖chart0 a b
        ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖)⁻¹ :=
      mul_nonneg x.1.2.1 (le_of_lt (inv_pos.mpr hv))
    linarith

lemma wFibH_ne_zero (a b : ℤ) (x : unitInterval × ↥(pW a b)) : wFibH a b x ≠ 0 := by
  intro h
  have h' : wFibH a b x = 0 := h
  rcases smul_eq_zero.mp (show ((1 - (x.1 : ℝ)) + (x.1 : ℝ) *
      (‖chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖)⁻¹) •
      chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace) = 0 from h') with h2 | h2
  · exact absurd h2 (ne_of_gt (wFibCoef_pos a b x))
  · exact absurd h2 (chart0_ne_zero a b _ x.2.2.1)

lemma wBaseH_mem (a b : ℤ) (x : unitInterval × ↥(pW a b)) :
    wBaseH a b x ∈ Work.Agree.hemi0 ∩ Work.Agree.hemi1 := by
  refine ⟨OnePoint.coe_ne_infty _, fun h => ?_⟩
  rcases smul_eq_zero.mp (OnePoint.coe_injective h) with h2 | h2
  · exact (ne_of_gt (wBaseCoef_pos a b x)) h2
  · exact (coord0_wB_ne_zero a b x.2) h2

/-- The point of `pW` at time `t` of the deformation. -/
def wHom (a b : ℤ) (x : unitInterval × ↥(pW a b)) : ↥(pW a b) :=
  ⟨⟨⟨wBaseH a b x, wFibH a b x⟩, wFibH_ne_zero a b x⟩, wBaseH_mem a b x⟩

lemma continuous_chart0_pW (a b : ℤ) :
    Continuous fun x : unitInterval × ↥(pW a b) =>
      chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace) :=
  (continuousOn_chart0 a b).comp_continuous
    ((Continuous.comp
      (continuous_subtype_val :
        Continuous (Subtype.val : ↥(Work.Thom.zeroComplement (Zb a b)) →
          (Zb a b).TotalSpace))
      (continuous_subtype_val :
        Continuous (Subtype.val : ↥(pW a b) → ↥(Work.Thom.zeroComplement (Zb a b))))).comp
      continuous_snd)
    (fun x => x.2.2.1)

lemma continuous_wB (a b : ℤ) : Continuous fun p : ↥(pW a b) => wB a b p :=
  ((Zb a b).continuous_proj).comp
    (Continuous.comp
      (continuous_subtype_val :
        Continuous (Subtype.val : ↥(Work.Thom.zeroComplement (Zb a b)) →
          (Zb a b).TotalSpace))
      (continuous_subtype_val :
        Continuous (Subtype.val : ↥(pW a b) → ↥(Work.Thom.zeroComplement (Zb a b)))))

lemma continuous_wBaseH (a b : ℤ) : Continuous (wBaseH a b) := by
  refine OnePoint.continuous_coe.comp ?_
  have hcoord : Continuous fun x : unitInterval × ↥(pW a b) =>
      Work.Agree.coord0 (wB a b x.2) :=
    Work.Agree.continuousOn_coord0.comp_continuous
      ((continuous_wB a b).comp continuous_snd) (fun x => wB_mem0 a b x.2)
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((hcoord.norm).inv₀ (fun x => norm_ne_zero_iff.mpr (coord0_wB_ne_zero a b x.2))))).smul
    hcoord

lemma continuous_wFibH (a b : ℤ) : Continuous (wFibH a b) := by
  have hchart := continuous_chart0_pW a b
  have hc : Continuous fun x : unitInterval × ↥(pW a b) =>
      (1 - (x.1 : ℝ)) + (x.1 : ℝ) *
        (‖chart0 a b ((x.2 : ↥(pW a b)) : (Zb a b).TotalSpace)‖)⁻¹ :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((hchart.norm).inv₀ (fun x => norm_ne_zero_iff.mpr (chart0_ne_zero a b _ x.2.2.1))))
  exact hc.smul hchart

theorem continuous_wHom (a b : ℤ) : Continuous (wHom a b) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk
      (Geo.continuous_mk_hemi0 a b ⟨wBaseH a b, continuous_wBaseH a b⟩
        (fun x => (wBaseH_mem a b x).1) ⟨wFibH a b, continuous_wFibH a b⟩)
      (wFibH_ne_zero a b))
    (wBaseH_mem a b)

theorem wHom_zero (a b : ℤ) (p : ↥(pW a b)) : wHom a b (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  refine Geo.totalSpace_ext a b ?_ ?_
  · show wBaseH a b (0, p) = wB a b p
    simp only [wBaseH]
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, zero_mul, add_zero, one_smul,
      Work.Agree.coord0_mem (wB_mem0 a b p)]
  · show (show EuclideanSpace ℝ (Fin 4) from wFibH a b (0, p)) =
      (show EuclideanSpace ℝ (Fin 4) from (p : (Zb a b).TotalSpace).2)
    simp only [wFibH]
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, zero_mul, add_zero, one_smul,
      chart0_of_mem a b (wB_mem0 a b p)]

theorem wHom_one (a b : ℤ) (p : ↥(pW a b)) : wHom a b (1, p) = sW a b (rhoW a b p) := by
  apply Subtype.ext
  apply Subtype.ext
  refine Geo.totalSpace_ext a b ?_ ?_
  · show wBaseH a b (1, p) =
      (↑(Work.Agree.ofQ (((rhoW a b p).1 : MV.S3Q) : Quaternion ℝ)) : Work.Agree.S4)
    simp only [wBaseH]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_add, one_mul]
    rw [show (((rhoW a b p).1 : MV.S3Q) : Quaternion ℝ) =
      Work.Agree.toQ (dir0 (wB a b p)) from rfl, Work.Agree.ofQ_toQ]
    rfl
  · show (show EuclideanSpace ℝ (Fin 4) from wFibH a b (1, p)) =
      (show EuclideanSpace ℝ (Fin 4) from
        ((sW a b (rhoW a b p) : ↥(pW a b)) : (Zb a b).TotalSpace).2)
    simp only [wFibH]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_add, one_mul]
    rw [show ((sW a b (rhoW a b p) : ↥(pW a b)) : (Zb a b).TotalSpace).2 =
      Work.Agree.ofQ (((rhoW a b p).2 : MV.S3Q) : Quaternion ℝ) from
      localTriv_false_symm a b (OnePoint.coe_ne_infty _) _]
    rw [show (((rhoW a b p).2 : MV.S3Q) : Quaternion ℝ) =
      Work.Agree.toQ (nrmlz (chart0 a b (p : (Zb a b).TotalSpace))) from rfl,
      chart0_of_mem a b (wB_mem0 a b p), Work.Agree.ofQ_toQ]
    rfl

/-- **The deformation of `pW` onto the image of its section.** -/
def wHomotopy (a b : ℤ) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(pW a b)) ((sW a b).comp (rhoW a b)) :=
  ContinuousMap.Homotopy.mk ⟨wHom a b, continuous_wHom a b⟩ (wHom_zero a b) (wHom_one a b)

/-- **The pullback of `rhoW` is an isomorphism.** -/
theorem bijective_HMap_rhoW (a b : ℤ) (n : ℕ) :
    Function.Bijective (HMap (rhoW a b) n).hom := by
  have hinj : (HMap (sW a b) n).hom.comp (HMap (rhoW a b) n).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (HMap_comp (sW a b) (rhoW a b) n)
    rw [ModuleCat.hom_comp] at h
    rw [← h, rhoW_sW, HMap_id, ModuleCat.hom_id]
  have hsurj : (HMap (rhoW a b) n).hom.comp (HMap (sW a b) n).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (HMap_comp (rhoW a b) (sW a b) n)
    rw [ModuleCat.hom_comp] at h
    rw [← h, HMap_homotopic ⟨(wHomotopy a b).symm⟩ n, HMap_id, ModuleCat.hom_id]
  constructor
  · intro x y hxy
    have hx := LinearMap.congr_fun hinj x
    have hy := LinearMap.congr_fun hinj y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, hxy, hy]
  · intro y
    exact ⟨(HMap (sW a b) n).hom y, LinearMap.congr_fun hsurj y⟩

/-! ## 6. The compatibility of `rhoV` with the inclusion of the overlap (the clutching) -/

lemma toQ_nrmlz (v : EuclideanSpace ℝ (Fin 4)) :
    Work.Agree.toQ (nrmlz v) = ‖v‖⁻¹ • Work.Agree.toQ v := by
  rw [nrmlz, map_smul]

lemma toQ_nrmlz_ofQ (w : Quaternion ℝ) :
    Work.Agree.toQ (nrmlz (Work.Agree.ofQ w)) = ‖w‖⁻¹ • w := by
  rw [nrmlz, map_smul, Work.Agree.toQ_ofQ]
  rw [show ‖Work.Agree.ofQ w‖ = ‖w‖ from by
    show ‖Quaternion.linearIsometryEquivTuple w‖ = ‖w‖
    exact Quaternion.linearIsometryEquivTuple.norm_map w]

lemma uDir_eq_toQ_dir0 (a b : ℤ) (p : ↥(pW a b)) :
    Work.Agree.uDir (wB a b p) = Work.Agree.toQ (dir0 (wB a b p)) := by
  rw [Work.Agree.uDir_eq_dirVal (wB_mem0 a b p) (wB_mem1 a b p), Work.Milnor.dirVal, dir0,
    nrmlz]
  show (‖Work.Agree.coord0 (wB a b p)‖ : ℝ)⁻¹ •
      Quaternion.linearIsometryEquivTuple.symm (Work.Agree.coord0 (wB a b p)) =
    Work.Agree.toQ ((‖Work.Agree.coord0 (wB a b p)‖ : ℝ)⁻¹ • Work.Agree.coord0 (wB a b p))
  rw [map_smul]
  rfl

lemma norm_uDir (a b : ℤ) (p : ↥(pW a b)) : ‖Work.Agree.uDir (wB a b p)‖ = 1 :=
  Submission.Milnor.norm_coe (Submission.Milnor.unitDir (Work.Agree.coord0 (wB a b p)))

lemma norm_toQ (v : EuclideanSpace ℝ (Fin 4)) : ‖Work.Agree.toQ v‖ = ‖v‖ :=
  Quaternion.linearIsometryEquivTuple.symm.norm_map v

lemma chart1_eq (a b : ℤ) (p : ↥(pW a b)) :
    chart1 a b (p : (Zb a b).TotalSpace) =
      Work.Agree.qTwist a b (Work.Agree.uDir (wB a b p)) (wV a b p) := by
  rw [chart1_apply, VectorBundleCore.localTriv_apply]
  rw [show (Zb a b).indexAt ((p : (Zb a b).TotalSpace).1) = false from if_neg (wB_mem0 a b p)]
  rw [Work.Agree.clutchBundle_coordChange_false_true]
  rfl

theorem rhoV_iotaV (a b : ℤ) :
    (rhoV a b).comp (MV.iotaV a b) = (psi a b).comp (rhoW a b) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  show Work.Agree.toQ (nrmlz (chart1 a b (p : (Zb a b).TotalSpace))) =
    ((rhoW a b p).1 : Quaternion ℝ) ^ a * (((rhoW a b p).2 : MV.S3Q) : Quaternion ℝ) *
      ((rhoW a b p).1 : Quaternion ℝ) ^ b
  rw [show ((rhoW a b p).1 : Quaternion ℝ) = Work.Agree.toQ (dir0 (wB a b p)) from rfl,
    show (((rhoW a b p).2 : MV.S3Q) : Quaternion ℝ) =
      Work.Agree.toQ (nrmlz (chart0 a b (p : (Zb a b).TotalSpace))) from rfl,
    chart0_of_mem a b (wB_mem0 a b p)]
  rw [chart1_eq a b p, Work.Agree.qTwist_apply, toQ_nrmlz_ofQ, uDir_eq_toQ_dir0 a b p]
  -- the norm of the argument of `nrmlz` is the norm of the fibre coordinate
  have hnorm : ‖Work.Agree.toQ (dir0 (wB a b p)) ^ a * Work.Agree.toQ (wV a b p) *
      Work.Agree.toQ (dir0 (wB a b p)) ^ b‖ = ‖wV a b p‖ := by
    have hq1 : ‖Work.Agree.toQ (dir0 (wB a b p))‖ = 1 := by
      rw [norm_toQ, dir0, norm_nrmlz (Work.Agree.coord0_ne_zero (wB_mem0 a b p)
        (wB_mem1 a b p))]
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, hq1]
    simp [norm_toQ]
  rw [hnorm, toQ_nrmlz, mul_smul_comm, smul_mul_assoc]
  rfl


/-! ## 7. The pullback of `rhoV` is onto

The retraction `rhoV : pV → S³` is the composite of the first-chart trivialisation `pV ≅ hemi1 ×
(ℝ⁴∖0)` with the normalisation of the fibre coordinate; `hemi1` is contractible and the
normalisation is a homotopy equivalence, so its pullback is onto. -/

/-- The radial normalisation, as a continuous map. -/
def nrmlzC : C(H4.Punc, Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  toFun v := ⟨nrmlz v.1, nrmlz_mem_sphere v.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuousOn_nrmlz.comp_continuous continuous_subtype_val
      (fun v => v.2)) (fun v => nrmlz_mem_sphere v.2)

/-- The inverse homeomorphism `S³(ℝ⁴) ≅ S³(ℍ)`. -/
def s3symmC : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, MV.S3Q) :=
  ⟨fun w => Work.CharacteristicClasses.s3Homeo.symm w,
    Work.CharacteristicClasses.s3Homeo.symm.continuous⟩

/-- The projection `↥hemi1 × Punc → Punc`. -/
def sndC : C(↥(Work.Agree.hemi1) × H4.Punc, H4.Punc) := ⟨Prod.snd, continuous_snd⟩

/-- **The normalisation is a homotopy equivalence.** -/
theorem isIso_HMap_nrmlz (n : ℕ) : IsIso (HMap nrmlzC n) := by
  have hincl : ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      (v : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
    intro v h0
    have h := Metric.mem_sphere.mp v.2
    rw [dist_zero_right, h0, norm_zero] at h
    norm_num at h
  let incl : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, H4.Punc) :=
    ⟨fun v => ⟨v.1, hincl v⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  have hpos : ∀ x : unitInterval × H4.Punc,
      0 < (1 - (x.1 : ℝ)) + (x.1 : ℝ) * (‖x.2.1‖)⁻¹ := by
    intro x
    have hv : 0 < ‖x.2.1‖ := norm_pos_iff.mpr x.2.2
    rcases eq_or_lt_of_le x.1.2.2 with h2 | h2
    · rw [h2, sub_self, zero_add, one_mul]
      exact inv_pos.mpr hv
    · have h3 : 0 < 1 - (x.1 : ℝ) := by linarith
      have h4 : 0 ≤ (x.1 : ℝ) * (‖x.2.1‖)⁻¹ :=
        mul_nonneg x.1.2.1 (le_of_lt (inv_pos.mpr hv))
      linarith
  have hsec : Continuous fun x : unitInterval × H4.Punc => x.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have ht : Continuous fun x : unitInterval × H4.Punc => (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hinv : Continuous fun x : unitInterval × H4.Punc => (‖x.2.1‖)⁻¹ :=
    (hsec.norm).inv₀ (fun x => by
      intro h0
      exact x.2.2 (norm_eq_zero.mp h0))
  let Hfun : C(unitInterval × H4.Punc, H4.Punc) :=
    ⟨fun x => ⟨((1 - (x.1 : ℝ)) + (x.1 : ℝ) * (‖x.2.1‖)⁻¹) • x.2.1,
        smul_ne_zero (ne_of_gt (hpos x)) x.2.2⟩,
      Continuous.subtype_mk (((continuous_const.sub ht).add (ht.mul hinv)).smul hsec) _⟩
  have h1 : ((ContinuousMap.id H4.Punc)).Homotopic ((incl.comp nrmlzC)) := by
    refine ⟨ContinuousMap.Homotopy.mk Hfun ?_ ?_⟩
    · intro x
      apply Subtype.ext
      show ((1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * (‖x.1‖)⁻¹) • x.1 = x.1
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, zero_mul, add_zero, one_smul]
    · intro x
      apply Subtype.ext
      show ((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * (‖x.1‖)⁻¹) • x.1 =
        nrmlz x.1
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_add, one_mul, nrmlz]
  have h2eq : nrmlzC.comp incl = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro v
    apply Subtype.ext
    show nrmlz v.1 = v.1
    exact nrmlz_of_norm_eq_one (by
      have h := Metric.mem_sphere.mp v.2
      rwa [dist_zero_right] at h)
  have h2 : ((nrmlzC.comp incl)).Homotopic (ContinuousMap.id _) := by
    rw [h2eq]
  exact Work.Cohomology.homotopyEquiv ℤ (TopCat.of H4.Punc)
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (TopCat.ofHom nrmlzC) (TopCat.ofHom incl) h1.some.symm h2.some n

/-- A homeomorphism induces an isomorphism on cohomology. -/
theorem isIso_HMap_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) : IsIso (HMap (⟨e, e.continuous⟩ : C(X, Y)) n) := by
  have h1 : (((⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp (⟨e, e.continuous⟩ : C(X, Y)))).Homotopic
      (ContinuousMap.id X) := by
    rw [show ((⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp (⟨e, e.continuous⟩ : C(X, Y)))
      = ContinuousMap.id X from by ext x; exact e.symm_apply_apply x]
  have h2 : (((⟨e, e.continuous⟩ : C(X, Y)).comp (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))).Homotopic
      (ContinuousMap.id Y) := by
    rw [show ((⟨e, e.continuous⟩ : C(X, Y)).comp (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))
      = ContinuousMap.id Y from by ext y; exact e.apply_symm_apply y]
  exact Work.Cohomology.homotopyEquiv ℤ (TopCat.of X) (TopCat.of Y)
    (TopCat.ofHom ⟨e, e.continuous⟩) (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
    h1.some h2.some n

/-- The pullback of `S³(ℝ⁴) ≅ S³(ℍ)` is an isomorphism. -/
theorem isIso_HMap_s3symmC (n : ℕ) : IsIso (HMap s3symmC n) :=
  isIso_HMap_of_homeomorph Work.CharacteristicClasses.s3Homeo.symm n

/-- **The pullback of the projection `↥hemi1 × Punc → Punc` is an isomorphism** (the first factor
is contractible). -/
theorem isIso_HMap_sndC (n : ℕ) : IsIso (HMap sndC n) := by
  haveI : ContractibleSpace ↥(Work.Agree.hemi1) := HemiContractible1
  obtain ⟨x₀, hx₀⟩ := id_nullhomotopic ↥(Work.Agree.hemi1)
  let gC : C(H4.Punc, ↥(Work.Agree.hemi1) × H4.Punc) :=
    ⟨fun v => (x₀, v), continuous_const.prodMk continuous_id⟩
  have h1 : (gC.comp sndC).Homotopic (ContinuousMap.id _) :=
    hx₀.symm.prodMap (ContinuousMap.Homotopic.refl (ContinuousMap.id H4.Punc))
  have h2 : (sndC.comp gC).Homotopic (ContinuousMap.id _) := by
    rw [show sndC.comp gC = ContinuousMap.id H4.Punc from by ext v; rfl]
  exact Work.Cohomology.homotopyEquiv ℤ (TopCat.of (↥(Work.Agree.hemi1) × H4.Punc))
    (TopCat.of H4.Punc) (TopCat.ofHom sndC) (TopCat.ofHom gC) h1.some h2.some n

/-- The composite `(s3Homeo.symm ∘ nrmlz) ∘ snd`, the model of `rhoV` on the product. -/
def hVC (a b : ℤ) : C(↥(Work.Agree.hemi1) × H4.Punc, MV.S3Q) :=
  s3symmC.comp (nrmlzC.comp sndC)

/-- The pullback of the model of `rhoV` is onto. -/
theorem surjective_HMap_hVC (a b : ℤ) (n : ℕ) :
    Function.Surjective (HMap (hVC a b) n).hom := by
  have h1 : (HMap (hVC a b) n).hom
      = ((HMap (nrmlzC.comp sndC) n).hom).comp ((HMap s3symmC n).hom) := by
    rw [hVC, HMap_comp, ModuleCat.hom_comp]
  have h2 : (HMap (nrmlzC.comp sndC) n).hom
      = ((HMap sndC n).hom).comp ((HMap nrmlzC n).hom) := by
    rw [HMap_comp, ModuleCat.hom_comp]
  haveI := isIso_HMap_nrmlz n
  haveI := isIso_HMap_sndC n
  haveI := isIso_HMap_s3symmC n
  intro y
  obtain ⟨w, hw⟩ := (asIso (HMap sndC n)).toLinearEquiv.bijective.surjective y
  obtain ⟨u, hu⟩ := (asIso (HMap nrmlzC n)).toLinearEquiv.bijective.surjective w
  obtain ⟨x, hx⟩ := (asIso (HMap s3symmC n)).toLinearEquiv.bijective.surjective u
  refine ⟨x, ?_⟩
  rw [h1, h2]
  show ((asIso (HMap sndC n)).toLinearEquiv
    ((asIso (HMap nrmlzC n)).toLinearEquiv ((asIso (HMap s3symmC n)).toLinearEquiv x))) = y
  rw [hx, hu, hw]

/-- **`rhoV` is the model map composed with the first-chart trivialisation.** -/
theorem rhoV_comp_pVHomeo (a b : ℤ) :
    (rhoV a b).comp
        (⟨(H4.pVHomeo a b).symm, (H4.pVHomeo a b).symm.continuous⟩ :
          C(↥(Work.Agree.hemi1) × H4.Punc, ↥(pV a b))) = hVC a b := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  show Work.Agree.toQ (nrmlz (chart1 a b
      (((H4.pVHomeo a b).symm q : ↥(pV a b)) : (Zb a b).TotalSpace))) =
    Work.Agree.toQ (nrmlz (q.2.1))
  rw [show (((H4.pVHomeo a b).symm q : ↥(pV a b)) : (Zb a b).TotalSpace) =
    H4.symmAt true a b q from rfl]
  rw [show chart1 a b (H4.symmAt true a b q) = H4.chartI true a b (H4.symmAt true a b q) from rfl,
    H4.chartI_symmAt]

/-- **The pullback of `rhoV` is onto.** -/
theorem surjective_HMap_rhoV (a b : ℤ) (n : ℕ) :
    Function.Surjective (HMap (rhoV a b) n).hom := by
  have hcomp := rhoV_comp_pVHomeo a b
  have hpush : (rhoV a b) = (hVC a b).comp
      (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
        C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) := by
    apply ContinuousMap.ext
    intro p
    have hp : (H4.pVHomeo a b).symm ((H4.pVHomeo a b) p) = p :=
      (H4.pVHomeo a b).symm_apply_apply p
    calc (rhoV a b) p
        = (rhoV a b) ((H4.pVHomeo a b).symm ((H4.pVHomeo a b) p)) := by rw [hp]
      _ = ((rhoV a b).comp (⟨(H4.pVHomeo a b).symm, (H4.pVHomeo a b).symm.continuous⟩ :
            C(↥(Work.Agree.hemi1) × H4.Punc, ↥(pV a b)))) ((H4.pVHomeo a b) p) := rfl
      _ = (hVC a b) ((H4.pVHomeo a b) p) := by rw [hcomp]
  have hfac : (HMap (rhoV a b) n).hom
      = ((HMap (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
            C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) n).hom).comp
          ((HMap (hVC a b) n).hom) := by
    have h := congrArg ModuleCat.Hom.hom (HMap_comp
      (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
        C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) (hVC a b) n)
    rw [ModuleCat.hom_comp] at h
    rw [← hpush] at h
    exact h
  haveI : IsIso (HMap (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
      C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) n) :=
    isIso_HMap_of_homeomorph (H4.pVHomeo a b) n
  have hsurjΦ : Function.Surjective (HMap (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
      C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) n).hom := by
    intro z
    exact ⟨(asIso (HMap (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
        C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) n)).toLinearEquiv.symm z,
      (asIso (HMap (⟨(H4.pVHomeo a b), (H4.pVHomeo a b).continuous⟩ :
        C(↥(pV a b), ↥(Work.Agree.hemi1) × H4.Punc)) n)).toLinearEquiv.apply_symm_apply z⟩
  intro y
  obtain ⟨w, hw⟩ := hsurjΦ y
  obtain ⟨x, hx⟩ := surjective_HMap_hVC a b n w
  refine ⟨x, ?_⟩
  rw [hfac]
  simp only [LinearMap.comp_apply, hx, hw]

end Geo

end

end Work.Transgression
