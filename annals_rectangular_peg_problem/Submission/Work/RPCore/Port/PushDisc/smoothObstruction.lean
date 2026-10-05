import Mathlib
import Submission.Work.RPCore.Port.PushDisc.conicalFluxMachinery
import Submission.Work.RPCore.Port.PushDisc.coneVolumeInvariance
import Submission.Work.RPCore.Port.PushDisc.conicalFamilies

/-!
# The smooth obstruction on the even spheres

For odd `d` there is no smooth sphere-valued homotopy of the unit sphere of
`E = EuclideanSpace ℝ (Fin d)` which avoids the antipodal map at time `0` and the identity at
time `1`.  This is the "smooth form" of the fact that the degree of the identity differs from the
degree of the antipodal map on an even sphere.

The proof chains the invariance of the conical signed volume `coneVol` along the three straight-line
families `fam1`, `fam2`, `fam3` of `conicalFamilies.lean`, and evaluates
`coneVol id = ∫ χ > 0` against `coneVol (-id) = (-1)^d ∫ χ < 0`.
-/

namespace Work.RPCore.Port.PushDisc

open scoped Matrix Topology
open MeasureTheory Filter

variable {d : ℕ}

/-! ## The cone extension of the identity and of the antipodal map -/

lemma coneExt_id :
    coneExt (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = id := by
  funext y
  rcases eq_or_ne y 0 with rfl | hy
  · simp [coneExt]
  · rw [coneExt, unitize]
    show ‖y‖ • ((‖y‖)⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

lemma coneExt_neg :
    coneExt (fun x : EuclideanSpace ℝ (Fin d) => -x) = fun x => -x := by
  funext y
  rcases eq_or_ne y 0 with rfl | hy
  · simp [coneExt]
  · have h1 : -(unitize y) = (-(‖y‖)⁻¹) • y := by rw [unitize, neg_smul]
    rw [coneExt, h1, smul_smul, mul_neg, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), neg_one_smul]

/-! ## The determinant of the Jacobian at the two ends -/

lemma fderiv_neg_id (y : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => -z) y
      = (-1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin d) => -z)
      = -(id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) := rfl
  rw [h1, fderiv_neg, fderiv_id]
  rfl

lemma jacM_fst_det (y : EuclideanSpace ℝ (Fin d)) :
    (jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2) (0, y)).det = 1 := by
  have hM : jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2) (0, y)
      = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i l
    rw [Matrix.one_apply]
    simp only [jacM]
    have hslice : (fun z : EuclideanSpace ℝ (Fin d) =>
        (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2) (0, z)) = id := rfl
    rw [hslice, fderiv_id]
    simp [stdV, PiLp.single_apply]
  rw [hM, Matrix.det_one]

lemma jacM_neg_fst_det (y : EuclideanSpace ℝ (Fin d)) :
    (jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => -p.2) (0, y)).det = (-1 : ℝ) ^ d := by
  have hM : jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => -p.2) (0, y)
      = -(1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i l
    rw [Matrix.neg_apply, Matrix.one_apply]
    simp only [jacM]
    have hslice : (fun z : EuclideanSpace ℝ (Fin d) =>
        (fun p : ℝ × EuclideanSpace ℝ (Fin d) => -p.2) (0, z)) = fun z : EuclideanSpace ℝ (Fin d) => -z := rfl
    rw [hslice, fderiv_neg_id]
    simp [stdV, PiLp.single_apply]
  rw [hM, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]

/-! ## The positivity of the weighted volume -/

/-- The weighted volume `∫ χ` is positive. -/
lemma integral_chi_pos {d : ℕ} (hd : 1 ≤ d) : 0 < ∫ y : EuclideanSpace ℝ (Fin d), chi y := by
  have hint : Integrable (chi : EuclideanSpace ℝ (Fin d) → ℝ) volume :=
    contDiff_chi.continuous.integrable_of_hasCompactSupport (chi_hasCompactSupport (d := d))
  rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall chi_nonneg) hint]
  have hu : ‖(stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    rw [stdV, EuclideanSpace.norm_single]
    norm_num
  have hsub : Metric.ball (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d)) (1 / 4)
      ⊆ Function.support (chi : EuclideanSpace ℝ (Fin d) → ℝ) := by
    intro y hy
    rw [Function.mem_support]
    refine (chi_pos_of_mem ?_ ?_).ne'
    · have h1 : ‖y - (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))‖ < 1 / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have h2 := abs_norm_sub_norm_le y (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))
      rw [hu] at h2
      have h2' : |‖y‖ - 1| ≤ 1 / 4 := le_trans h2 h1.le
      have h3 : (3 : ℝ) / 4 ≤ ‖y‖ := by linarith [(abs_le.mp h2').1]
      nlinarith [norm_nonneg y]
    · have h1 : ‖y - (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))‖ < 1 / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have h2 := abs_norm_sub_norm_le y (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))
      rw [hu] at h2
      have h2' : |‖y‖ - 1| ≤ 1 / 4 := le_trans h2 h1.le
      have h3 : ‖y‖ ≤ (5 : ℝ) / 4 := by linarith [(abs_le.mp h2').2]
      nlinarith [norm_nonneg y]
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume (stdV ⟨0, hd⟩) (by norm_num)) (measure_mono hsub)

/-! ## The two values of the conical signed volume -/

lemma coneVol_id :
    coneVol (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) =
      ∫ y : EuclideanSpace ℝ (Fin d), chi y := by
  unfold coneVol
  have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        coneExt (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) p.2)
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2) := by
    funext p
    exact congrFun coneExt_id p.2
  rw [hfun]
  simp only [jacM_fst_det, mul_one]

lemma coneVol_neg_id :
    coneVol (fun x : EuclideanSpace ℝ (Fin d) => -x) =
      (-1 : ℝ) ^ d * ∫ y : EuclideanSpace ℝ (Fin d), chi y := by
  unfold coneVol
  have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        coneExt (fun x : EuclideanSpace ℝ (Fin d) => -x) p.2)
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => -p.2) := by
    funext p
    exact congrFun coneExt_neg p.2
  rw [hfun]
  simp only [jacM_neg_fst_det]
  rw [MeasureTheory.integral_mul_const]
  ring

/-! ## The endpoint identifications of the three families -/

lemma coneVol_fam1_zero (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    coneVol (fam1 H 0) = coneVol (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) := by
  refine coneVol_congr fun x hx => ?_
  rw [fam1, sub_zero, zero_smul, add_zero, one_smul, unitize_of_norm_one hx]
  rfl

lemma coneVol_fam1_one (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1) :
    coneVol (fam1 H 1) = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (0, x)) := by
  refine coneVol_congr fun x hx => ?_
  rw [fam1, sub_self, zero_smul, zero_add, one_smul, unitize_of_norm_one (hu 0 x hx)]

lemma coneVol_fam2_zero (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    coneVol (fam2 H 0) = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (0, x)) := by
  refine coneVol_congr fun x _ => rfl

lemma coneVol_fam2_one (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    coneVol (fam2 H 1) = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (1, x)) := by
  refine coneVol_congr fun x _ => rfl

lemma coneVol_fam3_zero (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1) :
    coneVol (fam3 H 0) = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (1, x)) := by
  refine coneVol_congr fun x hx => ?_
  rw [fam3, sub_zero, zero_smul, sub_zero, one_smul, unitize_of_norm_one (hu 1 x hx)]

lemma coneVol_fam3_one (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    coneVol (fam3 H 1) = coneVol (fun x : EuclideanSpace ℝ (Fin d) => -x) := by
  refine coneVol_congr fun x hx => ?_
  rw [fam3, sub_self, zero_smul, one_smul, zero_sub, unitize_of_norm_one (by simpa using hx)]

/-! ## The smooth obstruction -/

/-- **The smooth obstruction.**  For odd `d` there is no smooth sphere-valued homotopy of
`S^{d-1}` avoiding the antipodal map at time `0` and the identity at time `1`. -/
theorem no_smooth_avoiding_of_odd {d : ℕ} (hodd : Odd d) :
    ¬ ∃ H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
        (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (0, x) ≠ -x) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (1, x) ≠ x) := by
  rintro ⟨H, hsm, hu, h0, h1⟩
  have hu' : ∀ s : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → ‖H (s, x)‖ = 1 := hu
  have inv1 : coneVol (fam1 H 0) = coneVol (fam1 H 1) := by
    have h := coneVolume_invariant
      (Φ := fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam1 H p.1) p.2)
      (contDiffOn_coneExt_fam1 H hsm hu h0)
      (fun t r y hr => coneExt_smul (fam1 H t) hr y)
      (fun t y => norm_coneExt (fam1 H t) (fun x hx => fam1_norm H hu h0 t hx) y) 0 1
    rwa [coneVol_eq_family (fam1 H) 0, coneVol_eq_family (fam1 H) 1] at h
  have inv2 : coneVol (fam2 H 0) = coneVol (fam2 H 1) := by
    have h := coneVolume_invariant
      (Φ := fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam2 H p.1) p.2)
      (contDiffOn_coneExt_fam2 H hsm)
      (fun t r y hr => coneExt_smul (fam2 H t) hr y)
      (fun t y => norm_coneExt (fam2 H t) (fun x hx => fam2_norm H hu t hx) y) 0 1
    rwa [coneVol_eq_family (fam2 H) 0, coneVol_eq_family (fam2 H) 1] at h
  have inv3 : coneVol (fam3 H 0) = coneVol (fam3 H 1) := by
    have h := coneVolume_invariant
      (Φ := fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam3 H p.1) p.2)
      (contDiffOn_coneExt_fam3 H hsm hu h1)
      (fun t r y hr => coneExt_smul (fam3 H t) hr y)
      (fun t y => norm_coneExt (fam3 H t) (fun x hx => fam3_norm H hu h1 t hx) y) 0 1
    rwa [coneVol_eq_family (fam3 H) 0, coneVol_eq_family (fam3 H) 1] at h
  have key : coneVol (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      = coneVol (fun x : EuclideanSpace ℝ (Fin d) => -x) :=
    calc coneVol (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        = coneVol (fam1 H 0) := (coneVol_fam1_zero H).symm
      _ = coneVol (fam1 H 1) := inv1
      _ = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (0, x)) := coneVol_fam1_one H hu
      _ = coneVol (fam2 H 0) := (coneVol_fam2_zero H).symm
      _ = coneVol (fam2 H 1) := inv2
      _ = coneVol (fun x : EuclideanSpace ℝ (Fin d) => H (1, x)) := coneVol_fam2_one H
      _ = coneVol (fam3 H 0) := (coneVol_fam3_zero H hu).symm
      _ = coneVol (fam3 H 1) := inv3
      _ = coneVol (fun x : EuclideanSpace ℝ (Fin d) => -x) := coneVol_fam3_one H
  rw [coneVol_id, coneVol_neg_id, hodd.neg_one_pow] at key
  have hd1 : 1 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
  have hpos := integral_chi_pos (d := d) hd1
  linarith

end Work.RPCore.Port.PushDisc
