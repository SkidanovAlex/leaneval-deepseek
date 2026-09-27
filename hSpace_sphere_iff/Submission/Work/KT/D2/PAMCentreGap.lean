import Mathlib
import Submission.Work.KT.D2.PAMDefs

/-!
# The quantitative centre gap for the disc-model Hopf clutching family

This file proves `Work.KT.D2.PAMCentreGap`: for a continuous family `u` of invertible
`2 × 2` complex matrices over the closed disc `D²` which is compatible with the disc-model
Hopf idempotent `PyA` (i.e. `u y * e₀ = PyA y * u y` for every `y`, with `e₀ = diag(1,0)`),
there is a radius `ε < 1/4` such that for every `y` with `‖y‖ ≤ ε`

* `‖u y 0 0‖ < ‖u dctr 1 0‖ / 8`, and
* `‖u dctr 1 0‖ / 4 < ‖u y 1 0‖`.

The mathematics is purely a continuity argument at the centre of the disc `dctr = 0`:

* at the centre, `PyA dctr = diag(0,1)`, so the conjugation relation forces `u dctr 0 0 = 0`;
* since `u dctr` is invertible, its first column `(u dctr 0 0, u dctr 1 0)` is non-zero, hence
  `u dctr 1 0 ≠ 0`;
* the first column `y ↦ (u y 0 0, u y 1 0)` is continuous, so near the centre it stays close to
  `(0, u dctr 1 0)`: its first entry stays `< ‖u dctr 1 0‖ / 8` and its second entry stays
  `> ‖u dctr 1 0‖ / 4` by the reverse triangle inequality.
-/

namespace Work.KT.D2

open Matrix

noncomputable section

theorem PAMCentreGap (u : C(Work.KT.D2.Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * Work.KT.D2.e0 = Work.KT.D2.PyA y * u y) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      (∀ y : Work.KT.D2.Dc, ‖(y : Work.KT.D2.E2)‖ ≤ ε →
        ‖u y 0 0‖ < ‖u Work.KT.D2.dctr 1 0‖ / 8) ∧
      (∀ y : Work.KT.D2.Dc, ‖(y : Work.KT.D2.E2)‖ ≤ ε →
        ‖u Work.KT.D2.dctr 1 0‖ / 4 < ‖u y 1 0‖) := by
  -- At the centre the idempotent is `diag(0,1)`, so the `(0,0)`-entry vanishes.
  have h00 : u dctr 0 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (hconj dctr)
    simp [e0, PyA_ctr, Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  -- Invertibility of `u dctr` and `u dctr 0 0 = 0` force the `(1,0)`-entry to be non-zero.
  have h10 : u dctr 1 0 ≠ 0 := by
    have hdet : (u dctr).det ≠ 0 := by
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      exact hunit dctr
    intro h
    apply hdet
    rw [Matrix.det_fin_two, h00, h]
    ring
  have hb : 0 < ‖u dctr 1 0‖ := norm_pos_iff.mpr h10
  -- The two entries of the first column are continuous.
  have hcont00 : Continuous fun y : Dc => u y 0 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (0 : Fin 2)).comp u.continuous)
  have hcont10 : Continuous fun y : Dc => u y 1 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (1 : Fin 2)).comp u.continuous)
  obtain ⟨δ1, hδ1pos, hδ1⟩ :=
    Metric.continuousAt_iff.mp hcont00.continuousAt (‖u dctr 1 0‖ / 8) (by linarith)
  obtain ⟨δ2, hδ2pos, hδ2⟩ :=
    Metric.continuousAt_iff.mp hcont10.continuousAt (‖u dctr 1 0‖ / 4) (by linarith)
  refine ⟨min (min δ1 δ2) (1 / 8) / 2, ?_, ?_, ?_, ?_⟩
  · exact div_pos (lt_min (lt_min hδ1pos hδ2pos) (by norm_num)) (by norm_num)
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

end

end Work.KT.D2
