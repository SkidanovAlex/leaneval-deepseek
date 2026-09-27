import Mathlib
import Submission.Work.KT.D2.PAMDefs

namespace Work.KT.D2

open Matrix

/-- At the centre of the disc the conjugation relation forces the `(0,0)`-entry of `u` to
vanish: `u dctr * e0 = diag(0,1) * u dctr`. -/
lemma PAMCentreSmall_h00 (u : C(Work.KT.D2.Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hconj : ∀ y, u y * Work.KT.D2.e0 = Work.KT.D2.PyA y * u y) : u dctr 0 0 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (hconj dctr)
  simp [e0, PyA_ctr, Matrix.mul_apply, Fin.sum_univ_two] at h
  exact h

/-- At the centre of the disc the `(1,0)`-entry of the unitary `u` does not vanish: the matrix
`u dctr` is invertible and `u dctr 0 0 = 0`, so its determinant is `- (u dctr 0 1) * (u dctr 1 0)`. -/
lemma PAMCentreSmall_h10 (u : C(Work.KT.D2.Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * Work.KT.D2.e0 = Work.KT.D2.PyA y * u y) :
    u dctr 1 0 ≠ 0 := by
  have h00 : u dctr 0 0 = 0 := PAMCentreSmall_h00 u hconj
  have hdet : (u dctr).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    exact hunit dctr
  intro h
  apply hdet
  rw [Matrix.det_fin_two, h00, h]
  ring

/-- **Positivity of the centre entry.**  For the disc-model Hopf clutching family `u` there is a
radius `ε < 1/4` such that on the disc of radius `ε` the `(0,0)`-entry of `u` is strictly smaller
than half of `‖u dctr 1 0‖` while the `(1,0)`-entry stays strictly bigger than that same quantity. -/
theorem PAMCentreSmall (u : C(Work.KT.D2.Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * Work.KT.D2.e0 = Work.KT.D2.PyA y * u y) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      (∀ y : Work.KT.D2.Dc, ‖(y : Work.KT.D2.E2)‖ ≤ ε → ‖u y 0 0‖ < ‖u Work.KT.D2.dctr 1 0‖ / 2) ∧
      (∀ y : Work.KT.D2.Dc, ‖(y : Work.KT.D2.E2)‖ ≤ ε → ‖u Work.KT.D2.dctr 1 0‖ / 2 < ‖u y 1 0‖) := by
  have h00 : u dctr 0 0 = 0 := PAMCentreSmall_h00 u hconj
  have h10 : u dctr 1 0 ≠ 0 := PAMCentreSmall_h10 u hunit hconj
  have hηpos : 0 < ‖u dctr 1 0‖ := norm_pos_iff.mpr h10
  have hcont00 : Continuous fun y : Dc => u y 0 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (0 : Fin 2)).comp u.continuous)
  have hcont10 : Continuous fun y : Dc => u y 1 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (1 : Fin 2)).comp u.continuous)
  obtain ⟨δ1, hδ1pos, hδ1⟩ :=
    Metric.continuousAt_iff.mp hcont00.continuousAt (‖u dctr 1 0‖ / 2) (by linarith)
  obtain ⟨δ2, hδ2pos, hδ2⟩ :=
    Metric.continuousAt_iff.mp hcont10.continuousAt (‖u dctr 1 0‖ / 2) (by linarith)
  have hmpos : 0 < min (min δ1 δ2) (1 / 8) := lt_min (lt_min hδ1pos hδ2pos) (by norm_num)
  refine ⟨min (min δ1 δ2) (1 / 8) / 2, div_pos hmpos (by norm_num), ?_, ?_, ?_⟩
  · have hm : min (min δ1 δ2) (1 / 8) ≤ 1 / 8 := min_le_right _ _
    linarith
  · intro y hy
    have hdist : dist y dctr < δ1 := by
      rw [Subtype.dist_eq, dctr_coe, dist_zero_right]
      have hm : min (min δ1 δ2) (1 / 8) ≤ δ1 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have h := hδ1 hdist
    rwa [h00, dist_zero_right] at h
  · intro y hy
    have hdist : dist y dctr < δ2 := by
      rw [Subtype.dist_eq, dctr_coe, dist_zero_right]
      have hm : min (min δ1 δ2) (1 / 8) ≤ δ2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have h := hδ2 hdist
    have hle : ‖u dctr 1 0‖ - ‖u y 1 0‖ ≤ dist (u y 1 0) (u dctr 1 0) := by
      rw [dist_eq_norm, norm_sub_rev]
      exact le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
    linarith

end Work.KT.D2
