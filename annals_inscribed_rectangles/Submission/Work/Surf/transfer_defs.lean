import Mathlib
import Submission.Work.Surf.defs

/-!
# The geometry of the faces of the unit square

This file collects the vocabulary used by the perturbation lemmas
`Work.Surf.Trans.face_cluster`, `Work.Surf.Trans.face_persist` and
`Work.Surf.Trans.zeros_regular_persist`, which together prove
`Work.Surf.transfer_hypotheses`.

It contains:

* the elementary identities relating the determinant `Work.Drive.det2`, the inner product and the
  norm in the plane (Euclidean space `𝔼²`): notably `inner ℝ y v ^ 2 + det2 y v ^ 2 = ‖y‖² ‖v‖²`;
* the characterisation of the *open* ray `{r • v : 0 < r}` as `det2 y v = 0 ∧ 0 < ⟪y, v⟫` and of the
  closed ray `{r • v : 0 ≤ r}` as a closed set;
* the parametrisation `facePt i` of the four faces of the unit square, the outward-running direction
  `faceDirN i` of each face, and the elementary facts about them (membership in `sqBdry`, the
  coordinate conditions met on each face, injectivity, the derivative);
* the parametrised functions `faceDet H v i t = det2 (H (facePt i t)) v` and
  `faceInn H v i t = ⟪H (facePt i t), v⟫`, together with their continuity, their derivatives, and the
  bounds expressing how much they move when `H` and `fderiv H` are perturbed.
-/

namespace Work.Surf.Trans

open Set Metric
open scoped Topology

noncomputable section

/-- The plane, as a Euclidean space. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-! ## Coordinates, inner product, determinant, norm -/

/-- The first basis vector of the plane. -/
def e0 : E2 := EuclideanSpace.single (0 : Fin 2) 1

/-- The second basis vector of the plane. -/
def e1 : E2 := EuclideanSpace.single (1 : Fin 2) 1

@[simp] lemma e0_apply_zero : (e0 : E2) 0 = 1 := by simp [e0]
@[simp] lemma e0_apply_one : (e0 : E2) 1 = 0 := by simp [e0]
@[simp] lemma e1_apply_zero : (e1 : E2) 0 = 0 := by simp [e1]
@[simp] lemma e1_apply_one : (e1 : E2) 1 = 1 := by simp [e1]

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0]
lemma norm_e1 : ‖e1‖ = 1 := by simp [e1]

lemma coord_decomp (x : E2) : x = x 0 • e0 + x 1 • e1 := by
  ext j; fin_cases j <;> simp [e0, e1]

lemma eq_zero_iff_coord (x : E2) : x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · intro h; simp [h]
  · rintro ⟨h0, h1⟩
    rw [coord_decomp x, h0, h1]; simp

lemma inner_apply (x v : E2) : inner ℝ x v = x 0 * v 0 + x 1 * v 1 := by
  rw [PiLp.inner_apply]; simp [Fin.sum_univ_two]; ring

lemma norm_sq_apply (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [Fin.sum_univ_two, sq]

/-- The classical identity `⟪y, v⟫² + det2 y v ² = ‖y‖² ‖v‖²` in the plane. -/
theorem inner_sq_add_det2_sq (y v : E2) :
    inner ℝ y v ^ 2 + Work.Drive.det2 y v ^ 2 = ‖y‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_apply, norm_sq_apply, norm_sq_apply, Work.Drive.det2]; ring

theorem abs_det2_le (u v : E2) : |Work.Drive.det2 u v| ≤ ‖u‖ * ‖v‖ := by
  have h := inner_sq_add_det2_sq u v
  have h2 : Work.Drive.det2 u v ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [sq_nonneg (inner ℝ u v)]
  calc |Work.Drive.det2 u v| = Real.sqrt (Work.Drive.det2 u v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((‖u‖ * ‖v‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖u‖ * ‖v‖ := Real.sqrt_sq (by positivity)

theorem det2_sub_left (u w v : E2) :
    Work.Drive.det2 (u - w) v = Work.Drive.det2 u v - Work.Drive.det2 w v := by
  simp only [Work.Drive.det2, PiLp.sub_apply]; ring

theorem det2_eq_zero_of_smul_self (c : ℝ) (v : E2) : Work.Drive.det2 (c • v) v = 0 := by
  simp only [Work.Drive.det2, PiLp.smul_apply, smul_eq_mul]; ring

/-- `y ↦ det2 y v` as a continuous linear functional. -/
def det2CLM (v : E2) : E2 →L[ℝ] ℝ :=
  (v 1) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) - (v 0) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)

lemma det2CLM_apply (v u : E2) : det2CLM v u = Work.Drive.det2 u v := by
  simp only [det2CLM, sub_apply, smul_apply, PiLp.proj_apply, Work.Drive.det2]
  ring

lemma continuous_det2_right (v : E2) : Continuous fun y : E2 => Work.Drive.det2 y v := by
  have h : (fun y : E2 => Work.Drive.det2 y v) = fun y : E2 => det2CLM v y := by
    funext y; rw [det2CLM_apply]
  rw [h]; exact (det2CLM v).continuous

/-! ## The rays through the origin in the direction `v` -/

/-- The open ray spanned by `v`. -/
def posRay (v : E2) : Set E2 := {y | ∃ r : ℝ, 0 < r ∧ y = r • v}

/-- The closed ray spanned by `v`, described by the determinant and the inner product. -/
def closedRay (v : E2) : Set E2 := {y | Work.Drive.det2 y v = 0 ∧ 0 ≤ inner ℝ y v}

lemma mem_posRay_iff {v : E2} (hv : v ≠ 0) {y : E2} :
    y ∈ posRay v ↔ Work.Drive.det2 y v = 0 ∧ 0 < inner ℝ y v := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨det2_eq_zero_of_smul_self r v, ?_⟩
    rw [inner_smul_left]
    exact mul_pos hr (real_inner_self_pos.mpr hv)
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ, y = c • v := by
      refine ⟨(y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2), ?_⟩
      have hv' : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
        intro hz
        refine hv ?_
        have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
        have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
        rw [coord_decomp v, h0, h1]; simp
      have hden : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hv')
      have hh : y 0 * v 1 - y 1 * v 0 = 0 := h1
      ext j
      fin_cases j
      · show y 0 = ((y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 0
        rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
        linear_combination (v 1) * hh
      · show y 1 = ((y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 1
        rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
        linear_combination (-(v 0)) * hh
    refine ⟨c, ?_, hc⟩
    have h2' : 0 < c * inner ℝ v v := by
      rw [hc, inner_smul_left] at h2
      simpa using h2
    have h3 : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    nlinarith

lemma mem_closedRay_iff {v : E2} (hv : v ≠ 0) {y : E2} :
    y ∈ closedRay v ↔ ∃ r : ℝ, 0 ≤ r ∧ y = r • v := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ, y = c • v := by
      refine ⟨(y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2), ?_⟩
      have hv' : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
        intro hz
        refine hv ?_
        have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
        have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
        rw [coord_decomp v, h0, h1]; simp
      have hden : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hv')
      have hh : y 0 * v 1 - y 1 * v 0 = 0 := h1
      ext j
      fin_cases j
      · show y 0 = ((y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 0
        rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
        linear_combination (v 1) * hh
      · show y 1 = ((y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 1
        rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
        linear_combination (-(v 0)) * hh
    refine ⟨c, ?_, hc⟩
    have h2' : 0 ≤ c * inner ℝ v v := by
      rw [hc, inner_smul_left] at h2
      simpa using h2
    have h3 : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    nlinarith
  · rintro ⟨r, hr, rfl⟩
    refine ⟨det2_eq_zero_of_smul_self r v, ?_⟩
    rw [inner_smul_left]
    simpa using mul_nonneg hr (real_inner_self_pos.mpr hv).le

lemma isClosed_closedRay (v : E2) : IsClosed (closedRay v) := by
  have h : closedRay v = {y : E2 | Work.Drive.det2 y v = 0} ∩ {y : E2 | 0 ≤ inner ℝ y v} := rfl
  rw [h]
  refine IsClosed.inter (isClosed_eq (continuous_det2_right v) continuous_const) ?_
  exact isClosed_le continuous_const (by fun_prop)

/-- A point on neither the negative ray nor the positive ray is at a positive distance from the
closed ray. -/
lemma exists_ball_disjoint_closedRay {v : E2} {y : E2} (hy : y ∉ closedRay v) :
    ∃ ρ > 0, ∀ z : E2, ‖z - y‖ < ρ → z ∉ closedRay v := by
  have hnhds : (closedRay v)ᶜ ∈ 𝓝 y := (isClosed_closedRay v).isOpen_compl.mem_nhds hy
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hnhds
  exact ⟨ρ, hρpos, fun z hz hzc => hρ (by rwa [Metric.mem_ball, dist_eq_norm]) hzc⟩

lemma eq_zero_of_det2_eq_zero_of_inner_eq_zero {v y : E2} (hv : v ≠ 0)
    (h1 : Work.Drive.det2 y v = 0) (h2 : inner ℝ y v = 0) : y = 0 := by
  have h := inner_sq_add_det2_sq y v
  rw [h1, h2] at h
  have hv' : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have h3 : ‖y‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])

/-! ## The four faces of the unit square -/

/-- The bottom face `{(t, 0)}`. -/
abbrev fb (t : ℝ) : E2 := t • e0
/-- The top face `{(t, 1)}`. -/
abbrev ft (t : ℝ) : E2 := t • e0 + e1
/-- The left face `{(0, t)}`. -/
abbrev fl (t : ℝ) : E2 := t • e1
/-- The right face `{(1, t)}`. -/
abbrev fr (t : ℝ) : E2 := e0 + t • e1

/-- The parametrisation of the `i`-th face of the unit square, for `i = 0, 1, 2, 3`
(bottom, top, left, right). -/
def facePt (i : Fin 4) (t : ℝ) : E2 :=
  if i.val = 0 then fb t else if i.val = 1 then ft t else if i.val = 2 then fl t else fr t

/-- The direction in which the `i`-th face runs. -/
def faceDirN (i : Fin 4) : E2 := if i.val ≤ 1 then e0 else e1

@[simp] lemma facePt_zero (t : ℝ) : facePt 0 t = fb t := by simp [facePt]
@[simp] lemma facePt_one (t : ℝ) : facePt 1 t = ft t := by simp [facePt]
@[simp] lemma facePt_two (t : ℝ) : facePt 2 t = fl t := by simp [facePt]
@[simp] lemma facePt_three (t : ℝ) : facePt 3 t = fr t := by simp [facePt]

@[simp] lemma faceDirN_zero : faceDirN 0 = e0 := by simp [faceDirN]
@[simp] lemma faceDirN_one : faceDirN 1 = e0 := by simp [faceDirN]
@[simp] lemma faceDirN_two : faceDirN 2 = e1 := by simp [faceDirN]
@[simp] lemma faceDirN_three : faceDirN 3 = e1 := by simp [faceDirN]

lemma continuous_fb : Continuous (fb : ℝ → E2) := by unfold fb; fun_prop
lemma continuous_ft : Continuous (ft : ℝ → E2) := by unfold ft; fun_prop
lemma continuous_fl : Continuous (fl : ℝ → E2) := by unfold fl; fun_prop
lemma continuous_fr : Continuous (fr : ℝ → E2) := by unfold fr; fun_prop

lemma continuous_facePt (i : Fin 4) : Continuous (facePt i) := by
  fin_cases i
  · show Continuous fb; exact continuous_fb
  · show Continuous ft; exact continuous_ft
  · show Continuous fl; exact continuous_fl
  · show Continuous fr; exact continuous_fr

lemma facePt_mem_sqBox (i : Fin 4) (t : ℝ) : facePt i t ∈ sqBox ↔ t ∈ Icc 0 1 := by
  fin_cases i <;> simp [facePt, sqBox, fb, ft, fl, fr]

lemma facePt_mem_sqBdry (i : Fin 4) {t : ℝ} (ht : t ∈ Icc 0 1) : facePt i t ∈ sqBdry := by
  refine ⟨(facePt_mem_sqBox i t).mpr ht, ?_⟩
  fin_cases i <;> simp [facePt, fb, ft, fl, fr]

@[simp] lemma fb_zero : (fb 0 : E2) = 0 := by simp [fb]
@[simp] lemma fl_zero : (fl 0 : E2) = 0 := by simp [fl]
@[simp] lemma ft_one : (ft 1 : E2) = e0 + e1 := by simp [ft]

lemma facePt_inj (i : Fin 4) : Function.Injective (facePt i) := by
  intro a b h
  fin_cases i
  · have := congrArg (fun x : E2 => x 0) h; simpa [facePt, fb] using this
  · have := congrArg (fun x : E2 => x 0) h; simpa [facePt, ft] using this
  · have := congrArg (fun x : E2 => x 1) h; simpa [facePt, fl] using this
  · have := congrArg (fun x : E2 => x 1) h; simpa [facePt, fr, e0] using this

lemma sqBdry_subset_iUnion_face : sqBdry ⊆ ⋃ i, facePt i '' Icc 0 1 := by
  intro x hx
  obtain ⟨hxbox, hdisj⟩ := hx
  rcases hdisj with h | h | h | h
  · refine mem_iUnion.mpr ⟨2, x 1, hxbox.2, ?_⟩
    have hx' : x = x 1 • e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    show fl (x 1) = x
    exact hx'.symm
  · refine mem_iUnion.mpr ⟨3, x 1, hxbox.2, ?_⟩
    have hx' : x = e0 + x 1 • e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    show fr (x 1) = x
    exact hx'.symm
  · refine mem_iUnion.mpr ⟨0, x 0, hxbox.1, ?_⟩
    have hx' : x = x 0 • e0 := by ext j; fin_cases j <;> simp [h, e0, e1]
    show fb (x 0) = x
    exact hx'.symm
  · refine mem_iUnion.mpr ⟨1, x 0, hxbox.1, ?_⟩
    have hx' : x = x 0 • e0 + e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    show ft (x 0) = x
    exact hx'.symm

lemma norm_faceDirN (i : Fin 4) : ‖faceDirN i‖ = 1 := by
  fin_cases i <;> simp [faceDirN, norm_e0, norm_e1]

lemma hasDerivAt_facePt (i : Fin 4) (t : ℝ) : HasDerivAt (facePt i) (faceDirN i) t := by
  have h0 : HasDerivAt (fun t : ℝ => t • e0) e0 t := by
    simpa using (hasDerivAt_id t).smul_const (e0 : E2)
  have h2 : HasDerivAt (fun t : ℝ => t • e1) e1 t := by
    simpa using (hasDerivAt_id t).smul_const (e1 : E2)
  have h1 : HasDerivAt (fun t : ℝ => t • e0 + e1) e0 t := by
    simpa using ((hasDerivAt_id t).smul_const (e0 : E2)).add_const (e1 : E2)
  have h3 : HasDerivAt (fun t : ℝ => e0 + t • e1) e1 t := by
    exact ((hasDerivAt_const (x := t) (c := e0)).add
      ((hasDerivAt_id t).smul_const (e1 : E2))).congr_deriv (by simp)
  fin_cases i
  · show HasDerivAt fb e0 t; exact h0
  · show HasDerivAt ft e0 t; exact h1
  · show HasDerivAt fl e1 t; exact h2
  · show HasDerivAt fr e1 t; exact h3

lemma fderiv_facePt (i : Fin 4) (t : ℝ) :
    fderiv ℝ (facePt i) t = ContinuousLinearMap.toSpanSingleton ℝ (faceDirN i) :=
  (hasDerivAt_facePt i t).hasFDerivAt.fderiv

lemma facePt_not_corner (i : Fin 4) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ¬ (((facePt i t) 0 = 0 ∨ (facePt i t) 0 = 1) ∧
       ((facePt i t) 1 = 0 ∨ (facePt i t) 1 = 1)) := by
  fin_cases i <;> simp [facePt, fb, ft, fl, fr, ht.1.ne', ht.2.ne]

lemma facePt_corner_iff (i : Fin 4) {t : ℝ} :
    (((facePt i t) 0 = 0 ∨ (facePt i t) 0 = 1) ∧
       ((facePt i t) 1 = 0 ∨ (facePt i t) 1 = 1)) ↔ (t = 0 ∨ t = 1) := by
  fin_cases i <;> simp [facePt, fb, ft, fl, fr]

lemma facePt_coord_one_iff (i : Fin 4) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ((facePt i t) 1 = 0 ∨ (facePt i t) 1 = 1) ↔ i.val ≤ 1 := by
  fin_cases i <;> simp [facePt, fb, ft, fl, fr, ht.1.ne', ht.2.ne]

lemma facePt_coord_zero_iff (i : Fin 4) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ((facePt i t) 0 = 0 ∨ (facePt i t) 0 = 1) ↔ ¬ (i.val ≤ 1) := by
  fin_cases i <;> simp [facePt, fb, ft, fl, fr, ht.1.ne', ht.2.ne]

/-! ## The ray-meeting parameters of a face -/

/-- The parameters `t ∈ [0,1]` at which `H` takes a value on the open ray spanned by `v` at the point
`facePt i t` of the `i`-th face. -/
def FaceRaySet (H : E2 → E2) (v : E2) (i : Fin 4) : Set ℝ :=
  {t : ℝ | t ∈ Icc 0 1 ∧ ∃ r : ℝ, 0 < r ∧ H (facePt i t) = r • v}

lemma FaceRaySet_eq (H : E2 → E2) {v : E2} (hv : v ≠ 0) (i : Fin 4) :
    FaceRaySet H v i = {t : ℝ | t ∈ Icc 0 1 ∧ Work.Drive.det2 (H (facePt i t)) v = 0 ∧
      0 < inner ℝ (H (facePt i t)) v} := by
  ext t
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mem_posRay_iff hv).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mem_posRay_iff hv).mpr h2⟩

lemma facePt_mem_rayMeet_of_mem (H : E2 → E2) (v : E2) {i : Fin 4} {t : ℝ}
    (ht : t ∈ FaceRaySet H v i) : facePt i t ∈ rayMeet H v ∩ sqBdry :=
  ⟨ht.2, facePt_mem_sqBdry i ht.1⟩

lemma rayMeet_inter_sqBdry_subset_iUnion (H : E2 → E2) (v : E2) :
    rayMeet H v ∩ sqBdry ⊆ ⋃ i, facePt i '' FaceRaySet H v i := by
  rintro x ⟨hx, hxb⟩
  obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp (sqBdry_subset_iUnion_face hxb)
  exact mem_iUnion.mpr ⟨i, t, ⟨ht, hx⟩, rfl⟩

lemma iUnion_facePt_image_subset_rayMeet_inter (H : E2 → E2) (v : E2) :
    (⋃ i, facePt i '' FaceRaySet H v i) ⊆ rayMeet H v ∩ sqBdry :=
  iUnion_subset fun i => image_subset_iff.mpr fun t ht => facePt_mem_rayMeet_of_mem H v ht

lemma rayMeet_inter_sqBdry_eq_iUnion (H : E2 → E2) (v : E2) :
    rayMeet H v ∩ sqBdry = ⋃ i, facePt i '' FaceRaySet H v i :=
  Subset.antisymm (rayMeet_inter_sqBdry_subset_iUnion H v)
    (iUnion_facePt_image_subset_rayMeet_inter H v)

/-! ## The parametrised determinant and inner product, and their calculus -/

/-- The determinant of `H` against `v`, along the `i`-th face of the square, as a function of the
face parameter. -/
def faceDet (H : E2 → E2) (v : E2) (i : Fin 4) : ℝ → ℝ := fun t => Work.Drive.det2 (H (facePt i t)) v

/-- The inner product of `H` with `v`, along the `i`-th face of the square. -/
def faceInn (H : E2 → E2) (v : E2) (i : Fin 4) : ℝ → ℝ := fun t => inner ℝ (H (facePt i t)) v

@[simp] lemma faceDet_apply (H : E2 → E2) (v : E2) (i : Fin 4) (t : ℝ) :
    faceDet H v i t = Work.Drive.det2 (H (facePt i t)) v := rfl

@[simp] lemma faceInn_apply (H : E2 → E2) (v : E2) (i : Fin 4) (t : ℝ) :
    faceInn H v i t = inner ℝ (H (facePt i t)) v := rfl

lemma continuous_faceDet (H : E2 → E2) (hH : Continuous H) (v : E2) (i : Fin 4) :
    Continuous (faceDet H v i) :=
  (continuous_det2_right v).comp (hH.comp (continuous_facePt i))

lemma continuous_faceInn (H : E2 → E2) (hH : Continuous H) (v : E2) (i : Fin 4) :
    Continuous (faceInn H v i) := by
  show Continuous fun t => inner ℝ (H (facePt i t)) v
  exact (hH.comp (continuous_facePt i)).inner continuous_const

lemma hasDerivAt_faceDet (H : E2 → E2) (hH : ContDiff ℝ 1 H) (v : E2) (i : Fin 4) (t : ℝ) :
    HasDerivAt (faceDet H v i) (Work.Drive.det2 (fderiv ℝ H (facePt i t) (faceDirN i)) v) t := by
  have h1 : HasDerivAt (fun t : ℝ => H (facePt i t))
      ((fderiv ℝ H (facePt i t)) (faceDirN i)) t := by
    have hd : DifferentiableAt ℝ H (facePt i t) := (hH.differentiable (by norm_num)).differentiableAt
    simpa [Function.comp_def] using hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_facePt i t)
  have h2 : HasDerivAt (fun t : ℝ => Work.Drive.det2 (H (facePt i t)) v)
      (Work.Drive.det2 ((fderiv ℝ H (facePt i t)) (faceDirN i)) v) t := by
    simpa [Function.comp_def, det2CLM_apply] using
      (ContinuousLinearMap.hasFDerivAt (det2CLM v)).comp_hasDerivAt t h1
  exact h2

lemma deriv_faceDet (H : E2 → E2) (hH : ContDiff ℝ 1 H) (v : E2) (i : Fin 4) (t : ℝ) :
    deriv (faceDet H v i) t = Work.Drive.det2 (fderiv ℝ H (facePt i t) (faceDirN i)) v :=
  (hasDerivAt_faceDet H hH v i t).deriv

lemma continuous_deriv_faceDet (H : E2 → E2) (hH : ContDiff ℝ 1 H) (v : E2) (i : Fin 4) :
    Continuous fun t => deriv (faceDet H v i) t := by
  have h1 : Continuous fun t : ℝ => fderiv ℝ H (facePt i t) :=
    (hH.continuous_fderiv (by norm_num)).comp (continuous_facePt i)
  have h2 : Continuous fun t : ℝ => (fderiv ℝ H (facePt i t)) (faceDirN i) :=
    h1.clm_apply continuous_const
  have h3 : Continuous fun t : ℝ => Work.Drive.det2 ((fderiv ℝ H (facePt i t)) (faceDirN i)) v :=
    (continuous_det2_right v).comp h2
  refine h3.congr fun t => ?_
  exact (deriv_faceDet H hH v i t).symm

lemma faceDet_sub (H F : E2 → E2) (v : E2) (i : Fin 4) (t : ℝ) :
    faceDet H v i t - faceDet F v i t
      = Work.Drive.det2 (H (facePt i t) - F (facePt i t)) v := by
  simp only [faceDet, det2_sub_left]

lemma abs_faceDet_sub_le (H F : E2 → E2) (v : E2) (i : Fin 4) (t : ℝ) :
    |faceDet H v i t - faceDet F v i t| ≤ ‖H (facePt i t) - F (facePt i t)‖ * ‖v‖ := by
  rw [faceDet_sub]; exact abs_det2_le _ _

lemma det2_sub_apply (A B : E2 →L[ℝ] E2) (d v : E2) :
    Work.Drive.det2 ((A - B) d) v = Work.Drive.det2 (A d) v - Work.Drive.det2 (B d) v := by
  have h : (A - B) d = A d - B d := by simp
  rw [h, det2_sub_left]

lemma deriv_faceDet_sub (H F : E2 → E2) (hH : ContDiff ℝ 1 H) (hF : ContDiff ℝ 1 F)
    (v : E2) (i : Fin 4) (t : ℝ) :
    deriv (faceDet H v i) t - deriv (faceDet F v i) t
      = Work.Drive.det2 ((fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)) (faceDirN i)) v := by
  rw [deriv_faceDet H hH, deriv_faceDet F hF, det2_sub_apply]

lemma abs_deriv_faceDet_sub_le (H F : E2 → E2) (hH : ContDiff ℝ 1 H) (hF : ContDiff ℝ 1 F)
    (v : E2) (i : Fin 4) (t : ℝ) :
    |deriv (faceDet H v i) t - deriv (faceDet F v i) t|
      ≤ ‖fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)‖ * ‖v‖ := by
  rw [deriv_faceDet_sub H F hH hF v i t]
  calc |Work.Drive.det2 ((fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)) (faceDirN i)) v|
      ≤ ‖(fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)) (faceDirN i)‖ * ‖v‖ :=
        abs_det2_le _ _
    _ ≤ (‖fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)‖ * ‖faceDirN i‖) * ‖v‖ := by
        have h := ContinuousLinearMap.le_opNorm
          (fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)) (faceDirN i)
        have hnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
        nlinarith
    _ = ‖fderiv ℝ H (facePt i t) - fderiv ℝ F (facePt i t)‖ * ‖v‖ := by
        rw [norm_faceDirN i, mul_one]

lemma abs_faceInn_sub_le (H F : E2 → E2) (v : E2) (i : Fin 4) (t : ℝ) :
    |faceInn H v i t - faceInn F v i t| ≤ ‖H (facePt i t) - F (facePt i t)‖ * ‖v‖ := by
  simp only [faceInn, ← inner_sub_left]
  exact abs_real_inner_le_norm _ _

/-! ## Two compactness helpers -/

/-- A strictly positive continuous function on a nonempty compact set has a positive lower bound. -/
lemma exists_pos_le_of_isCompact_of_pos {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    {K : Set α} (hf : Continuous f) (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    exact ⟨f x, hpos x hxK, fun t ht => hxmin ht⟩

/-- The minimum of a positive function over a finite type. -/
lemma exists_pos_le_of_finite {ι : Type*} (hι : Finite ι) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ c i := by
  haveI := hι
  rcases isEmpty_or_nonempty ι with hι' | hι'
  · exact ⟨1, one_pos, fun i => (hι'.false i).elim⟩
  · haveI : Fintype ι := Fintype.ofFinite ι
    refine ⟨Finset.univ.inf' Finset.univ_nonempty c, ?_, fun i => Finset.inf'_le c (Finset.mem_univ i)⟩
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hc i

end

end Work.Surf.Trans
