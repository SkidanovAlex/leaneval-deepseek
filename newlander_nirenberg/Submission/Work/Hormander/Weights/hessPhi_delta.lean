import Mathlib
import Submission.Work.Hormander.Weights.Basic
import Submission.Work.Hormander.Weights.dCoord_dbarCoord_comm

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

/-! ### Regularity of the coordinate derivatives -/

/-- If `u` is `C²` then `∂_j u` is `C¹` (hence in particular differentiable). -/
private lemma contDiff_one_dCoord {n : ℕ} (u : Cn n → ℂ) (hu : ContDiff ℝ 2 u) (j : Fin n) :
    ContDiff ℝ 1 (dCoord n j u) := by
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ u z) := hu.fderiv_right (m := 1) (by norm_num)
  have hA : ContDiff ℝ 1 (fun z => fderiv ℝ u z (evec n j)) :=
    (ContinuousLinearMap.apply ℝ ℂ (evec n j)).contDiff.comp h1
  have hB : ContDiff ℝ 1 (fun z => fderiv ℝ u z (ivec n j)) :=
    (ContinuousLinearMap.apply ℝ ℂ (ivec n j)).contDiff.comp h1
  change ContDiff ℝ 1 (fun z => (1 / 2 : ℂ) *
      (fderiv ℝ u z (evec n j) - Complex.I * fderiv ℝ u z (ivec n j)))
  exact contDiff_const.mul (hA.sub (contDiff_const.mul hB))

/-- If `u` is `C²` then `∂̄_j u` is `C¹` (hence in particular differentiable). -/
private lemma contDiff_one_dbarCoord {n : ℕ} (u : Cn n → ℂ) (hu : ContDiff ℝ 2 u) (j : Fin n) :
    ContDiff ℝ 1 (dbarCoord n j u) := by
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ u z) := hu.fderiv_right (m := 1) (by norm_num)
  have hA : ContDiff ℝ 1 (fun z => fderiv ℝ u z (evec n j)) :=
    (ContinuousLinearMap.apply ℝ ℂ (evec n j)).contDiff.comp h1
  have hB : ContDiff ℝ 1 (fun z => fderiv ℝ u z (ivec n j)) :=
    (ContinuousLinearMap.apply ℝ ℂ (ivec n j)).contDiff.comp h1
  change ContDiff ℝ 1 (fun z => (1 / 2 : ℂ) *
      (fderiv ℝ u z (evec n j) + Complex.I * fderiv ℝ u z (ivec n j)))
  exact contDiff_const.mul (hA.add (contDiff_const.mul hB))

theorem hessPhi_delta {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 2 φ) (f : Form1 n)
    (hf : ∀ j, ContDiff ℝ 2 (f j)) (j k : Fin n) (z : Cn n) :
    dCoord n j (dbarCoord n k (f j)) z
      - dbarCoord n k (fun w => dCoord n j (f j) w - f j w * dPhi n j φ w) z
      - dbarCoord n k (f j) z * dPhi n j φ z
      = f j z * hessPhi n j k φ z := by
  set u : Cn n → ℂ := f j with hu_def
  have hu : ContDiff ℝ 2 u := hf j
  have hφc : ContDiff ℝ 2 (fun w => (φ w : ℂ)) :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ
  have hu_diff : DifferentiableAt ℝ u z := (hu.contDiffAt.differentiableAt (by norm_num))
  have hψ_diff : DifferentiableAt ℝ (dPhi n j φ) z :=
    ((contDiff_one_dCoord (fun w => (φ w : ℂ)) hφc j).differentiable_one).differentiableAt
  have hA : DifferentiableAt ℝ (dCoord n j u) z :=
    ((contDiff_one_dCoord u hu j).differentiable_one).differentiableAt
  have hB : DifferentiableAt ℝ (fun w => u w * dPhi n j φ w) z := hu_diff.mul hψ_diff
  have hfun : (fun w => dCoord n j u w - u w * dPhi n j φ w)
      = (dCoord n j u - fun w => u w * dPhi n j φ w) := by
    funext w; rfl
  have hsub : dbarCoord n k (fun w => dCoord n j u w - u w * dPhi n j φ w) z
      = dbarCoord n k (dCoord n j u) z - dbarCoord n k (fun w => u w * dPhi n j φ w) z := by
    rw [hfun]
    exact dbarCoord_sub k (dCoord n j u) (fun w => u w * dPhi n j φ w) z hA hB
  have hmul : dbarCoord n k (fun w => u w * dPhi n j φ w) z
      = dbarCoord n k u z * dPhi n j φ z + u z * dbarCoord n k (dPhi n j φ) z :=
    dbarCoord_mul k u (dPhi n j φ) z hu_diff hψ_diff
  have hcomm : dCoord n j (dbarCoord n k u) z = dbarCoord n k (dCoord n j u) z :=
    dCoord_dbarCoord_comm j k u hu z
  have hphi : dbarCoord n k (dPhi n j φ) z = hessPhi n j k φ z :=
    (dCoord_dbarCoord_comm j k (fun w => (φ w : ℂ)) hφc z).symm
  rw [hsub, hmul, hcomm, hphi]
  ring

end Work.Hormander.Weights
