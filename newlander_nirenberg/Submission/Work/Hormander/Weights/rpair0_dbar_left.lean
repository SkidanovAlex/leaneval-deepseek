import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.normSq0_dbarStar
import Submission.Work.Hormander.Weights.normSq2_dbarForm
import Submission.Work.Hormander.Weights.pairing_dbar

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem rpair0_dbar_left {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n)
    (X Y : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y) :
    rpair0 φ (fun z => dbarCoord n j X z) Y
      = -rpair0 φ X (fun z => dCoord n j Y z)
        + rpair0 φ (fun z => X z * dbarPhi n j φ z) Y := by
  have hstarY : Continuous (fun z => star (Y z)) := continuous_star.comp hY.continuous
  have hdbarPhi : Continuous (fun z => dbarPhi n j φ z) :=
    continuous_dbarCoord (contDiff_ofReal_comp hφ) j
  have hA : Integrable (fun z => dbarCoord n j X z * star (Y z) * wn n φ z) :=
    integrable_mul_wn hφ ((continuous_dbarCoord hX j).mul hstarY)
      ((hasCompactSupport_dbarCoord hsX j).mul_right)
  have hB : Integrable (fun z => X z * star (dCoord n j Y z) * wn n φ z) :=
    integrable_mul_wn hφ (hX.continuous.mul (continuous_star.comp (continuous_dCoord hY j)))
      (hsX.mul_right)
  have hC : Integrable (fun z => X z * dbarPhi n j φ z * star (Y z) * wn n φ z) :=
    integrable_mul_wn hφ ((hX.continuous.mul hdbarPhi).mul hstarY)
      ((hsX.mul_right).mul_right)
  have hp := pairing_dbar φ hφ j X Y hX hY hsX hsY
  have hre := congrArg Complex.re hp
  simp only [Complex.add_re, Complex.neg_re] at hre
  rw [rpair0_eq_re_pairing hA, rpair0_eq_re_pairing hB, rpair0_eq_re_pairing hC] at hre
  exact hre

end Work.Hormander.Weights
