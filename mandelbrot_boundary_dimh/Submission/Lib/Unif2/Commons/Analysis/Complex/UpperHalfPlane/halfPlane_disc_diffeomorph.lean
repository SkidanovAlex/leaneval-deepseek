import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Submission.Lib.Unif2.Commons.Analysis.Complex.UpperHalfPlane.uhpOpenDiffeomorph

noncomputable section
open scoped Manifold ContDiff UpperHalfPlane
open TopologicalSpace
open Complex

namespace Commons.Analysis.Complex.UpperHalfPlane

/-- The open upper half plane of `ℂ`, bundled as an open subset of `ℂ`. -/
private abbrev HPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | 0 < z.im}, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

/-- The open unit ball of `ℂ`, bundled as an open subset of `ℂ`. -/
private abbrev BallOpen : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩

/-- The Cayley transform `z ↦ (z - i) / (z + i)` on `ℂ`. -/
private def cayleyFun (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `w ↦ i (1 + w) / (1 - w)` on `ℂ`. -/
private def cayleyInvFun (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

private lemma add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have hz0 : (z + I).im = 0 := congrArg Complex.im h
  have : (z + I).im = z.im + 1 := by simp
  linarith

/-- The Cayley transform sends the upper half plane into the unit ball. -/
private lemma norm_cayley_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayleyFun z‖ < 1 := by
  unfold cayleyFun
  have hden_ne : z + I ≠ 0 := add_I_ne_zero_of_im_pos hz
  have hlt_norm : ‖z - I‖ < ‖z + I‖ := by
    have hA : normSq (z - I) = normSq z + 1 - 2 * z.im := by
      simp only [normSq_apply, sub_re, sub_im, I_re, I_im]
      ring
    have hB : normSq (z + I) = normSq z + 1 + 2 * z.im := by
      simp only [normSq_apply, add_re, add_im, I_re, I_im]
      ring
    have hlt : normSq (z - I) < normSq (z + I) := by
      rw [hA, hB]
      linarith
    have hlt2 : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
      simpa [normSq_eq_norm_sq] using hlt
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hlt2
  have hden_pos : 0 < ‖z + I‖ := norm_pos_iff.mpr hden_ne
  rw [norm_div]
  exact (div_lt_one hden_pos).mpr hlt_norm

private lemma one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have hw_eq' : (1 : ℂ) = w := sub_eq_zero.mp h
  have hw_eq : w = 1 := hw_eq'.symm
  have : ‖w‖ = (1 : ℝ) := by rw [hw_eq]; simp
  linarith

private lemma normSq_lt_one_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : normSq w < 1 := by
  rw [normSq_eq_norm_sq]
  simpa using (sq_lt_sq₀ (norm_nonneg w) zero_le_one).mpr hw

/-- The inverse Cayley transform sends the unit ball into the upper half plane. -/
private lemma im_cayleyInv_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyInvFun w).im := by
  have hw1 : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  have hnum : 0 < 1 - normSq w := by
    have hns : normSq w < 1 := normSq_lt_one_of_norm_lt_one hw
    linarith
  have hden : 0 < normSq (1 - w) := (Complex.normSq_pos).mpr hw1
  unfold cayleyInvFun
  rw [Complex.div_im]
  rw [← sub_div]
  refine div_pos ?_ hden
  have hnum_eq : (I * (1 + w)).im * (1 - w).re - (I * (1 + w)).re * (1 - w).im = 1 - normSq w := by
    simp only [Complex.I_mul_im, Complex.I_mul_re, add_im, add_re, sub_re, sub_im,
      Complex.one_re, Complex.one_im, normSq_apply]
    ring
  rw [hnum_eq]
  exact hnum

/-- `cayleyInvFun ∘ cayleyFun` is the identity on the upper half plane. -/
private lemma cayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : cayleyInvFun (cayleyFun z) = z := by
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_pos hz
  have hc1 : cayleyFun z ≠ 1 := by
    intro h1
    have hnorm : ‖cayleyFun z‖ = 1 := by simp [h1]
    linarith [norm_cayley_lt_one hz, hnorm]
  have hc1' : 1 - cayleyFun z ≠ 0 := sub_ne_zero.mpr hc1.symm
  unfold cayleyFun cayleyInvFun
  field_simp [hzI, hc1']
  ring

/-- `cayleyFun ∘ cayleyInvFun` is the identity on the unit ball. -/
private lemma cayley_cayleyInv {w : ℂ} (hw : ‖w‖ < 1) : cayleyFun (cayleyInvFun w) = w := by
  have hw1 : 1 - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  have hden2 : cayleyInvFun w + I ≠ 0 := by
    have hpos : 0 < (cayleyInvFun w).im := im_cayleyInv_pos hw
    intro h
    have hIm : (cayleyInvFun w).im + 1 = 0 := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold cayleyFun cayleyInvFun
  field_simp [hw1, hden2]
  ring

/-- The equivalence between the upper half plane and the unit ball given by the Cayley
transform. -/
private def cayleyEquiv : HPlaneOpen ≃ BallOpen where
  toFun z := ⟨cayleyFun (z : ℂ), by
    have hz : 0 < (z : ℂ).im := z.2
    simpa [Metric.mem_ball, dist_eq_norm] using norm_cayley_lt_one hz⟩
  invFun w := ⟨cayleyInvFun (w : ℂ), by
    have hw' : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := w.2
    rw [Metric.mem_ball, dist_eq_norm] at hw'
    have hw : ‖(w : ℂ)‖ < 1 := by simpa using hw'
    exact im_cayleyInv_pos hw⟩
  left_inv z := by
    ext
    exact cayleyInv_cayley z.2
  right_inv w := by
    ext
    have hw' : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := w.2
    rw [Metric.mem_ball, dist_eq_norm] at hw'
    have hw : ‖(w : ℂ)‖ < 1 := by simpa using hw'
    exact cayley_cayleyInv hw

private lemma contDiffAt_cayleyFun {z : ℂ} (hz : z + I ≠ 0) :
    ContDiffAt ℂ ∞ cayleyFun z := by
  unfold cayleyFun
  exact ContDiffAt.div (by fun_prop) (by fun_prop) hz

private lemma contDiffAt_cayleyInvFun {w : ℂ} (hw : 1 - w ≠ 0) :
    ContDiffAt ℂ ∞ cayleyInvFun w := by
  unfold cayleyInvFun
  have h1 : ContDiffAt ℂ ∞ (fun x : ℂ => I * (1 + x)) w := by fun_prop
  have h2 : ContDiffAt ℂ ∞ (fun x : ℂ => 1 - x) w := by fun_prop
  exact ContDiffAt.div h1 h2 hw

private lemma contMDiff_toBall :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      (cayleyEquiv : HPlaneOpen → BallOpen) := by
  rw [← ContMDiff.subtypeVal_comp_iff (U := BallOpen) (f := cayleyEquiv)
    (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ℂ)]
  change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
    (fun z : HPlaneOpen => cayleyFun (z : ℂ))
  intro z
  rw [contMDiffAt_subtype_iff]
  rw [contMDiffAt_iff_contDiffAt]
  exact contDiffAt_cayleyFun (add_I_ne_zero_of_im_pos z.2)

private lemma contMDiff_fromBall :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      (cayleyEquiv.symm : BallOpen → HPlaneOpen) := by
  rw [← ContMDiff.subtypeVal_comp_iff (U := HPlaneOpen) (f := cayleyEquiv.symm)
    (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ℂ)]
  change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
    (fun w : BallOpen => cayleyInvFun (w : ℂ))
  intro w
  rw [contMDiffAt_subtype_iff]
  rw [contMDiffAt_iff_contDiffAt]
  have hw' : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := w.2
  rw [Metric.mem_ball, dist_eq_norm] at hw'
  have hw : ‖(w : ℂ)‖ < 1 := by simpa using hw'
  exact contDiffAt_cayleyInvFun (one_sub_ne_zero_of_norm_lt_one hw)

/-- The Cayley transform is a diffeomorphism between the upper half plane (as an open subset
of `ℂ`) and the open unit ball. -/
private def cayleyDiffeomorph :
    HPlaneOpen ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ BallOpen := by
  refine { toEquiv := cayleyEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact contMDiff_toBall
  · exact contMDiff_fromBall

theorem halfPlane_disc_diffeomorph :
    Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯
      (⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ)) := by
  rcases uhpOpenDiffeomorph with ⟨e1⟩
  exact ⟨e1.trans cayleyDiffeomorph⟩

end Commons.Analysis.Complex.UpperHalfPlane