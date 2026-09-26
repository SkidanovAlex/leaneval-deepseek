import Mathlib
import Submission.Work.Drive.framePathDefs
import Submission.Work.Drive.framedPolarDefs
import Submission.Work.Drive.rodriguesInner
import Submission.Work.Drive.angleOfCosSin

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real

noncomputable section

/-!
# A path of orthonormal pairs from `(f1, f2)` to `(e1, e2)`

`Work.Drive.framePathExists` provides a `ContDiff ℝ ⊤` path `g` of orthonormal
pairs with `g 0 = (f1, f2)` and `g 1 = (e1, e2)`, for any orthonormal pair
`(f1, f2)`.  The construction is by two successive Rodrigues rotations:

* the first rotates `f1` to `e1` about the axis `f1 × e1` (or about `f2` when
  `f1` is already parallel to `e1`),
* the second rotates the image of `f2` to `e2` about the axis `e1`.

Because both factors are rotations, the path stays in the orthonormal pairs, so
the framed interpolation family `Work.Drive.framedSlice` has orthonormal frames
at every slice.
-/

/-! ## 1. Elementary facts about the coordinate frame -/

lemma norm_e1 : ‖(e1 : Space)‖ = 1 := by
  have h : ‖(e1 : Space)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [e1, Fin.sum_univ_three]
  nlinarith [norm_nonneg (e1 : Space)]

lemma norm_e2 : ‖(e2 : Space)‖ = 1 := by
  have h : ‖(e2 : Space)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [e2, Fin.sum_univ_three]
  nlinarith [norm_nonneg (e2 : Space)]

lemma inner_e1_e1 : inner ℝ (e1 : Space) e1 = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e1]
  norm_num

lemma inner_e2_e2 : inner ℝ (e2 : Space) e2 = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e2]
  norm_num

lemma inner_e1_e2 : inner ℝ (e1 : Space) e2 = 0 := by
  rw [inner_eq_dot]
  simp [e1, e2, dotProduct, Fin.sum_univ_three]

/-! ## 2. The Rodrigues rotation of a unit axis preserves the inner product -/

lemma norm_rodrigues {n : Space} (hn : ‖n‖ = 1) (α : ℝ) (x : Space) :
    ‖rodrigues n α x‖ = ‖x‖ := by
  have h : inner ℝ (rodrigues n α x) (rodrigues n α x) = inner ℝ x x := rodriguesInner hn α
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (rodrigues n α x), norm_nonneg x]

@[simp] lemma rodrigues_zero (n : Space) (x : Space) : rodrigues n 0 x = x := by
  simp [rodrigues]

lemma rodrigues_axis {n : Space} (hn : ‖n‖ = 1) (α : ℝ) : rodrigues n α n = n := by
  have hnn : inner ℝ n n = 1 := by
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  rw [rodrigues, crossv_self, smul_zero, add_zero, hnn, mul_one, ← add_smul, add_sub_cancel,
    one_smul]

lemma inner_self_eq_zero_iff {z : Space} (h : inner ℝ z z = 0) : z = 0 := by
  have h2 : ‖z‖ = 0 := by
    have h3 : ‖z‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h
    nlinarith [norm_nonneg z]
  exact norm_eq_zero.mp h2

/-! ## 3. The orthonormal triple `(u, v, u × v)`: Parseval and expansion -/

lemma inner_smul_smul (a b : ℝ) (x y : Space) :
    inner ℝ (a • x) (b • y) = a * b * inner ℝ x y := by
  rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]

lemma inner_self_of_norm_one {x : Space} (h : ‖x‖ = 1) : inner ℝ x x = 1 := by
  rw [real_inner_self_eq_norm_sq, h]
  norm_num

lemma inner_sub_sub_self (a b : ℝ) (x y : Space) :
    inner ℝ (a • x - b • y) (a • x - b • y)
      = a ^ 2 * inner ℝ x x - 2 * (a * b) * inner ℝ x y + b ^ 2 * inner ℝ y y := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_smul, inner_smul_smul,
    inner_smul_smul, inner_smul_smul, real_inner_comm y x]
  ring

lemma inner_add_add_self (a b : ℝ) (x y : Space) :
    inner ℝ (a • x + b • y) (a • x + b • y)
      = a ^ 2 * inner ℝ x x + 2 * (a * b) * inner ℝ x y + b ^ 2 * inner ℝ y y := by
  rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_smul, inner_smul_smul,
    inner_smul_smul, inner_smul_smul, real_inner_comm y x]
  ring

/-- **Parseval for the orthonormal triple `(u, v, u × v)`**: for unit orthogonal
`u`, `v` the three coordinates of `w` in the orthonormal basis `(u, v, u × v)`
have squared sum `‖w‖ ^ 2`. -/
lemma parseval_crossv {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (w : Space) :
    (inner ℝ w u) ^ 2 + (inner ℝ w v) ^ 2 + (inner ℝ w (crossv u v)) ^ 2 = ‖w‖ ^ 2 := by
  have hvu : inner ℝ v u = 0 := by rw [← real_inner_comm v u]; exact huv
  have h1 : crossv (crossv u v) w = inner ℝ u w • v - inner ℝ v w • u := crossv_crossv u v w
  have hnorm : ‖crossv (crossv u v) w‖ ^ 2 = (inner ℝ w u) ^ 2 + (inner ℝ w v) ^ 2 := by
    rw [h1, real_inner_comm u w, real_inner_comm v w, ← real_inner_self_eq_norm_sq,
      inner_sub_sub_self, inner_self_of_norm_one hv, inner_self_of_norm_one hu, hvu]
    ring
  have hlag := norm_sq_crossv (crossv u v) w
  have hK : ‖crossv u v‖ ^ 2 = 1 := by
    rw [norm_sq_crossv, hu, hv, huv]
    ring
  rw [hK, one_mul, ← real_inner_comm (crossv u v) w] at hlag
  linarith [hnorm, hlag]

/-- **Expansion in the triple `(u, v, u × v)`**: a vector orthogonal to `u × v`
is the sum of its `u`- and `v`-components. -/
lemma eq_smul_add_of_inner_crossv {u v w : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (h : inner ℝ w (crossv u v) = 0) :
    w = (inner ℝ w u) • u + (inner ℝ w v) • v := by
  set a : ℝ := inner ℝ w u with ha
  set b : ℝ := inner ℝ w v with hb
  have hpar := parseval_crossv hu hv huv w
  have hab : a ^ 2 + b ^ 2 = ‖w‖ ^ 2 := by
    rw [← ha, ← hb, h] at hpar
    linarith [hpar]
  have hws : inner ℝ w (a • u + b • v) = a ^ 2 + b ^ 2 := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, ← ha, ← hb]
    ring
  have hss : inner ℝ (a • u + b • v) (a • u + b • v) = a ^ 2 + b ^ 2 := by
    rw [inner_add_add_self, inner_self_of_norm_one hu, inner_self_of_norm_one hv, huv]
    ring
  have hexp : inner ℝ (w - (a • u + b • v)) (w - (a • u + b • v))
      = inner ℝ w w - 2 * inner ℝ w (a • u + b • v)
        + inner ℝ (a • u + b • v) (a • u + b • v) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (a • u + b • v) w]
    ring
  have hzero : inner ℝ (w - (a • u + b • v)) (w - (a • u + b • v)) = 0 := by
    rw [hexp, real_inner_self_eq_norm_sq, hws, hss, hab]
    ring
  have hsub : w - (a • u + b • v) = 0 := inner_self_eq_zero_iff hzero
  simpa only [ha, hb] using sub_eq_zero.mp hsub

/-- For a unit vector `h` orthogonal to `e1`, the cross products with `e1`
invert each other: `h × (e1 × h) = e1`. -/
lemma crossv_crossv_e1 {h : Space} (hh : inner ℝ (e1 : Space) h = 0) (hn : ‖h‖ = 1) :
    crossv h (crossv (e1 : Space) h) = e1 := by
  have hh1 : inner ℝ h h = 1 := inner_self_of_norm_one hn
  rw [crossv_anticomm, crossv_crossv, hh, zero_smul, zero_sub, hh1]
  simp

/-! ## 4. The first rotation: bringing `f1` to `e1` -/

/-- The axis of the first rotation: `f1 × e1` when this is nonzero, and `f2`
otherwise (then `f1 = ± e1`, so a rotation by `π` about the axis `f2 ⊥ f1`
still carries `f1` to `e1`). -/
noncomputable def frameAxis (f1 f2 : Space) : Space :=
  if crossv f1 (e1 : Space) = 0 then f2
  else (‖crossv f1 (e1 : Space)‖)⁻¹ • crossv f1 (e1 : Space)

/-- The angle of the first rotation: the angle from `f1` to `e1`. -/
noncomputable def frameAngle1 (f1 : Space) : ℝ :=
  angleOf (inner ℝ f1 (e1 : Space)) ‖crossv f1 (e1 : Space)‖

lemma frameAngle1_spec {f1 : Space} (h1 : ‖f1‖ = 1) :
    Real.cos (frameAngle1 f1) = inner ℝ f1 (e1 : Space) ∧
      Real.sin (frameAngle1 f1) = ‖crossv f1 (e1 : Space)‖ := by
  have hunit : (inner ℝ f1 (e1 : Space)) ^ 2 + ‖crossv f1 (e1 : Space)‖ ^ 2 = 1 := by
    have h := norm_sq_crossv f1 (e1 : Space)
    rw [norm_e1, h1] at h
    nlinarith [h, norm_nonneg (crossv f1 (e1 : Space))]
  exact angleOfCosSin hunit

lemma frameAxis_norm {f1 f2 : Space} (h2 : ‖f2‖ = 1) : ‖frameAxis f1 f2‖ = 1 := by
  unfold frameAxis
  split
  · exact h2
  · rename_i hzero
    have hpos : 0 < ‖crossv f1 (e1 : Space)‖ := norm_pos_iff.mpr hzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
      inv_mul_cancel₀ (ne_of_gt hpos)]

lemma frameAxis_orth {f1 f2 : Space} (hperp : inner ℝ f1 f2 = 0) :
    inner ℝ (frameAxis f1 f2) f1 = 0 := by
  unfold frameAxis
  split
  · rename_i hzero
    rw [real_inner_comm f1 f2, hperp]
  · rw [real_inner_smul_left, inner_crossv_self, mul_zero]

/-- **The first rotation carries `f1` to `e1`.** -/
theorem rodrigues_frameAxis {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    rodrigues (frameAxis f1 f2) (frameAngle1 f1) f1 = e1 := by
  obtain ⟨hcos, hsin⟩ := frameAngle1_spec h1
  have hax : inner ℝ (frameAxis f1 f2) f1 = 0 := frameAxis_orth hperp
  rw [rodrigues, hcos, hsin, hax, mul_zero, zero_smul, add_zero]
  by_cases hzero : crossv f1 (e1 : Space) = 0
  · rw [frameAxis, if_pos hzero]
    have hnorm0 : ‖crossv f1 (e1 : Space)‖ = 0 := by rw [hzero]; simp
    rw [hnorm0, zero_smul, add_zero]
    have hc2 : (inner ℝ f1 (e1 : Space)) ^ 2 = 1 := by
      have h := norm_sq_crossv f1 (e1 : Space)
      rw [norm_e1, h1, hzero] at h
      simp at h
      linarith [h]
    have hfe : f1 = (inner ℝ f1 (e1 : Space)) • e1 := by
      have hsub : f1 - (inner ℝ f1 (e1 : Space)) • e1 = 0 := by
        apply inner_self_eq_zero_iff
        rw [show f1 - (inner ℝ f1 (e1 : Space)) • e1
            = (1 : ℝ) • f1 - (inner ℝ f1 (e1 : Space)) • e1 from by rw [one_smul],
          inner_sub_sub_self, one_pow, one_mul, inner_self_of_norm_one h1,
          inner_self_of_norm_one norm_e1]
        nlinarith [hc2]
      simpa using sub_eq_zero.mp hsub
    have hmul : inner ℝ f1 (e1 : Space) * inner ℝ f1 (e1 : Space) = 1 := by
      rw [← sq]
      exact hc2
    have hstep1 : (inner ℝ f1 (e1 : Space)) • f1
        = (inner ℝ f1 (e1 : Space)) • ((inner ℝ f1 (e1 : Space)) • e1) :=
      congrArg (fun z : Space => (inner ℝ f1 (e1 : Space)) • z) hfe
    have hstep2 : (inner ℝ f1 (e1 : Space)) • ((inner ℝ f1 (e1 : Space)) • e1) = e1 := by
      rw [smul_smul, hmul, one_smul]
    rw [hstep1, hstep2]
  · rw [frameAxis, if_neg hzero]
    have hpos : 0 < ‖crossv f1 (e1 : Space)‖ := norm_pos_iff.mpr hzero
    have hK : ‖crossv f1 (e1 : Space)‖ * (‖crossv f1 (e1 : Space)‖)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hpos)
    rw [crossv_smul_left, smul_smul, hK, one_smul, crossv_crossv, inner_self_of_norm_one h1,
      one_smul, ← real_inner_comm e1 f1]
    rw [add_sub_cancel]

/-! ## 5. The second rotation: bringing the image of `f2` to `e2` -/

/-- The image of `f2` under the first rotation. -/
noncomputable def frameMid (f1 f2 : Space) : Space :=
  rodrigues (frameAxis f1 f2) (frameAngle1 f1) f2

/-- The angle of the second rotation about the axis `e1`. -/
noncomputable def frameAngle2 (f1 f2 : Space) : ℝ :=
  angleOf (inner ℝ (frameMid f1 f2) (e2 : Space))
    (inner ℝ (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space))

lemma frameMid_norm {f1 f2 : Space} (h2 : ‖f2‖ = 1) : ‖frameMid f1 f2‖ = 1 := by
  rw [frameMid, norm_rodrigues (frameAxis_norm h2), h2]

lemma frameMid_orth {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) : inner ℝ (e1 : Space) (frameMid f1 f2) = 0 := by
  have h := rodriguesInner (frameAxis_norm (f1 := f1) h2) (frameAngle1 f1) (x := f1) (y := f2)
  rw [rodrigues_frameAxis h1 h2 hperp, hperp] at h
  simpa [frameMid] using h

lemma crossv_e1_mid_norm {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    ‖crossv (e1 : Space) (frameMid f1 f2)‖ = 1 := by
  have hh := frameMid_orth h1 h2 hperp
  have hn := frameMid_norm (f1 := f1) h2
  have h := norm_sq_crossv (e1 : Space) (frameMid f1 f2)
  rw [norm_e1, hn, hh] at h
  nlinarith [h, norm_nonneg (crossv (e1 : Space) (frameMid f1 f2))]

lemma inner_mid_crossv {f1 f2 : Space} :
    inner ℝ (frameMid f1 f2) (crossv (e1 : Space) (frameMid f1 f2)) = 0 := by
  rw [crossv_anticomm, inner_neg_right, inner_self_crossv, neg_zero]

lemma inner_e2_crossv_mid {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    inner ℝ (e2 : Space) (crossv (frameMid f1 f2) (crossv (e1 : Space) (frameMid f1 f2))) = 0 := by
  rw [crossv_crossv_e1 (frameMid_orth h1 h2 hperp) (frameMid_norm (f1 := f1) h2)]
  rw [real_inner_comm]
  exact inner_e1_e2

lemma frameAngle2_spec {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    Real.cos (frameAngle2 f1 f2) = inner ℝ (frameMid f1 f2) (e2 : Space) ∧
      Real.sin (frameAngle2 f1 f2)
        = inner ℝ (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space) := by
  have hunit : (inner ℝ (frameMid f1 f2) (e2 : Space)) ^ 2
      + (inner ℝ (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space)) ^ 2 = 1 := by
    have hpar := parseval_crossv (frameMid_norm (f1 := f1) h2) (crossv_e1_mid_norm h1 h2 hperp)
      inner_mid_crossv (e2 : Space)
    rw [inner_e2_crossv_mid h1 h2 hperp, norm_e2,
      show inner ℝ (e2 : Space) (frameMid f1 f2) = inner ℝ (frameMid f1 f2) (e2 : Space) from
        real_inner_comm (frameMid f1 f2) (e2 : Space),
      show inner ℝ (e2 : Space) (crossv (e1 : Space) (frameMid f1 f2))
          = inner ℝ (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space) from
        real_inner_comm (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space)] at hpar
    simpa using hpar
  exact angleOfCosSin hunit

/-- **The second rotation carries the image of `f2` to `e2`.** -/
theorem rodrigues_e1_frameMid {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    rodrigues (e1 : Space) (frameAngle2 f1 f2) (frameMid f1 f2) = e2 := by
  obtain ⟨hcos, hsin⟩ := frameAngle2_spec h1 h2 hperp
  have hh := frameMid_orth h1 h2 hperp
  have hn := frameMid_norm (f1 := f1) h2
  have hcn := crossv_e1_mid_norm h1 h2 hperp
  have hoch := inner_mid_crossv (f1 := f1) (f2 := f2)
  rw [rodrigues, hcos, hsin, hh, mul_zero, zero_smul, add_zero]
  have hexp := eq_smul_add_of_inner_crossv hn hcn hoch (w := (e2 : Space))
    (h := inner_e2_crossv_mid h1 h2 hperp)
  rw [show inner ℝ (frameMid f1 f2) (e2 : Space) = inner ℝ (e2 : Space) (frameMid f1 f2) from
      (real_inner_comm (frameMid f1 f2) (e2 : Space)).symm,
    show inner ℝ (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space)
        = inner ℝ (e2 : Space) (crossv (e1 : Space) (frameMid f1 f2)) from
      (real_inner_comm (crossv (e1 : Space) (frameMid f1 f2)) (e2 : Space)).symm,
    ← hexp]

/-! ## 6. The frame path -/

/-- The family of rotations carrying `(f1, f2)` to `(e1, e2)`; `s = 0` is the
identity and `s = 1` the target rotation. -/
noncomputable def frameMap (f1 f2 : Space) (s : ℝ) (x : Space) : Space :=
  rodrigues (e1 : Space) (s * frameAngle2 f1 f2)
    (rodrigues (frameAxis f1 f2) (s * frameAngle1 f1) x)

lemma frameMap_zero (f1 f2 : Space) (x : Space) : frameMap f1 f2 0 x = x := by
  simp [frameMap]

lemma frameMap_one_f1 {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) : frameMap f1 f2 1 f1 = e1 := by
  have h : frameMap f1 f2 1 f1 = rodrigues (e1 : Space) (frameAngle2 f1 f2)
      (rodrigues (frameAxis f1 f2) (frameAngle1 f1) f1) := by simp [frameMap]
  rw [h, rodrigues_frameAxis h1 h2 hperp, rodrigues_axis norm_e1]

lemma frameMap_one_f2 {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) : frameMap f1 f2 1 f2 = e2 := by
  have h : frameMap f1 f2 1 f2 = rodrigues (e1 : Space) (frameAngle2 f1 f2) (frameMid f1 f2) := by
    simp [frameMap, frameMid]
  rw [h, rodrigues_e1_frameMid h1 h2 hperp]

lemma frameMap_norm {f1 f2 : Space} (h2 : ‖f2‖ = 1) (s : ℝ) (x : Space) :
    ‖frameMap f1 f2 s x‖ = ‖x‖ := by
  rw [frameMap, norm_rodrigues norm_e1, norm_rodrigues (frameAxis_norm h2)]

lemma frameMap_inner {f1 f2 : Space} (h2 : ‖f2‖ = 1) (s : ℝ) (x y : Space) :
    inner ℝ (frameMap f1 f2 s x) (frameMap f1 f2 s y) = inner ℝ x y := by
  have ha : ‖frameAxis f1 f2‖ = 1 := frameAxis_norm (f1 := f1) h2
  show inner ℝ (rodrigues (e1 : Space) (s * frameAngle2 f1 f2)
        (rodrigues (frameAxis f1 f2) (s * frameAngle1 f1) x))
      (rodrigues (e1 : Space) (s * frameAngle2 f1 f2)
        (rodrigues (frameAxis f1 f2) (s * frameAngle1 f1) y)) = inner ℝ x y
  rw [rodriguesInner norm_e1 (s * frameAngle2 f1 f2), rodriguesInner ha (s * frameAngle1 f1)]

/-! ## 7. Analyticity in the path parameter -/

lemma contDiff_rodrigues_const {n : Space} {α : ℝ} {x : Space} :
    ContDiff ℝ ⊤ (fun s : ℝ => rodrigues n (s * α) x) := by
  unfold rodrigues
  fun_prop

lemma contDiff_inner_left (n : Space) :
    ContDiff ℝ ⊤ (fun x : Space => inner ℝ n x) := by
  have h : (fun x : Space => inner ℝ n x)
      = fun x : Space => n.ofLp 0 * x.ofLp 0 + n.ofLp 1 * x.ofLp 1 + n.ofLp 2 * x.ofLp 2 := by
    funext x
    rw [inner_eq_dot, dotProduct, Fin.sum_univ_three]
  rw [h]
  fun_prop

lemma contDiff_rodrigues {n : Space} {α : ℝ} {w : ℝ → Space} (hw : ContDiff ℝ ⊤ w) :
    ContDiff ℝ ⊤ (fun s : ℝ => rodrigues n (s * α) (w s)) := by
  have hcos : ContDiff ℝ ⊤ (fun s : ℝ => Real.cos (s * α)) := by fun_prop
  have hsin : ContDiff ℝ ⊤ (fun s : ℝ => Real.sin (s * α)) := by fun_prop
  have hcross : ContDiff ℝ ⊤ (fun s : ℝ => crossv n (w s)) := by
    rw [contDiff_piLp (p := 2)]
    intro i
    fin_cases i <;> simp [crossv, crossProduct] <;> fun_prop
  have hinner : ContDiff ℝ ⊤ (fun s : ℝ => inner ℝ n (w s)) :=
    (contDiff_inner_left n).comp hw
  rw [show (fun s : ℝ => rodrigues n (s * α) (w s))
      = fun s : ℝ => Real.cos (s * α) • w s + Real.sin (s * α) • crossv n (w s)
          + ((1 - Real.cos (s * α)) * inner ℝ n (w s)) • n from funext fun s => rfl]
  exact ((hcos.smul hw).add (hsin.smul hcross)).add
    (((contDiff_const.sub hcos).mul hinner).smul_const n)

lemma contDiff_frameMap (f1 f2 : Space) (x : Space) :
    ContDiff ℝ ⊤ (fun s : ℝ => frameMap f1 f2 s x) := by
  exact contDiff_rodrigues (n := e1) (α := frameAngle2 f1 f2) contDiff_rodrigues_const

/-- **A `ContDiff ℝ ⊤` path of orthonormal pairs from `(f1, f2)` to `(e1, e2)`.** -/
theorem framePathExists {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) :
    ∃ g : ℝ → Space × Space, ContDiff ℝ ⊤ g ∧ g 0 = (f1, f2) ∧ g 1 = (e1, e2) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, IsOrthoPair (g s).1 (g s).2 := by
  refine ⟨fun s : ℝ => (frameMap f1 f2 s f1, frameMap f1 f2 s f2), ?_, ?_, ?_, ?_⟩
  · exact (contDiff_frameMap f1 f2 f1).prodMk (contDiff_frameMap f1 f2 f2)
  · simp [frameMap_zero]
  · simp [frameMap_one_f1 h1 h2 hperp, frameMap_one_f2 h1 h2 hperp]
  · intro s hs
    exact ⟨by rw [frameMap_norm h2, h1], by rw [frameMap_norm h2, h2],
      by rw [frameMap_inner h2, hperp]⟩

end

end Work.Drive
