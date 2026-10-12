import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
import Submission.Work.BoseFixR.ChiR0Defs
import Submission.Work.BoseFixR.Rb5Lin.W1Facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory

theorem W1omegaMassLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1omegaFun v h ℓ x) ≤ 16 * Real.pi * BoseGases.a v := by
  have hnn : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      0 ≤ Work.BoseFixR.W1omegaFun v h ℓ z := by
    filter_upwards [Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR (fun x => hv x) hvrad hv_supp h]
      with z hz
    rw [Work.BoseB7AK.W1rows.W1omegaFun_eq]
    dsimp only [Submission.BoseGases.wScaled]
    rw [div_eq_mul_inv]
    exact mul_nonneg hz (inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg ℓ z))
  calc (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1omegaFun v h ℓ x)
      = ∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1omegaFun v h ℓ x| := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hnn] with z hz
        exact (abs_of_nonneg hz).symm
    _ ≤ 16 * Real.pi * BoseGases.a v :=
        Work.BoseB7AK.W1rows.W1omega_abs_integral_le hR hℓ (fun x => hv x) hvrad hv_supp h hRℓ

end Work.BoseFixR
