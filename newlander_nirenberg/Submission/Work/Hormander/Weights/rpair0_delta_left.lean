import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.normSq0_dbarStar
import Submission.Work.Hormander.Weights.normSq2_dbarForm
import Submission.Work.Hormander.Weights.pairing_delta

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem rpair0_delta_left {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n)
    (X Y : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y) :
    rpair0 φ (fun z => dCoord n j X z - X z * dPhi n j φ z) Y
      = -rpair0 φ X (fun z => dbarCoord n j Y z) := by
  have hstarY : Continuous (fun z => star (Y z)) := continuous_star.comp hY.continuous
  have hdPhi : Continuous (fun z => dPhi n j φ z) :=
    continuous_dCoord (contDiff_ofReal_comp hφ) j
  have hAc : Continuous (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)) :=
    ((continuous_dCoord hX j).sub (hX.continuous.mul hdPhi)).mul hstarY
  have hAcs : HasCompactSupport
      (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)) :=
    ((hasCompactSupport_dCoord hsX j).sub
      (hsX.mul_right (f' := fun z => dPhi n j φ z))).mul_right (f' := fun z => star (Y z))
  have hI1 : Integrable
      (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z) * wn n φ z) :=
    integrable_mul_wn hφ hAc hAcs
  have hI2 : Integrable (fun z => X z * star (dbarCoord n j Y z) * wn n φ z) :=
    integrable_mul_wn hφ (hX.continuous.mul (continuous_star.comp (continuous_dbarCoord hY j)))
      (hsX.mul_right (f' := fun z => star (dbarCoord n j Y z)))
  have hp := pairing_delta φ hφ j X Y hX hY hsX hsY
  have hre := congrArg Complex.re hp
  simp only [Complex.neg_re] at hre
  rw [rpair0_eq_re_pairing hI1, rpair0_eq_re_pairing hI2] at hre
  exact hre

end Work.Hormander.Weights
