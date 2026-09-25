import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral

open MeasureTheory
open scoped lp BigOperators ENNReal

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger

theorem opMul_apply_eq_integral
    (Φ : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) (m : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul Φ f hf m
      = ∫ θ : Work.BourgainPlan.IonescuWainger.Circle,
          ((Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) θ
            * (Work.BourgainPlan.IonescuWainger.ftLp f hf
                : Work.BourgainPlan.IonescuWainger.Circle → ℂ) θ
            * star (fourier m θ)) ∂(AddCircle.haarAddCircle (T := 1)) := by
  -- Recover the `m`-th coefficient of the multiplier through the coefficient–integral formula,
  -- then identify the Fourier transform of `opMul Φ f hf` with `Φ • 𝓕f`.
  rw [ftLp_coeff_integral (h := opMul Φ f hf) (opMul_memℓp Φ f hf) m, ftLp_opMul]
  simp only [opMulLp]
  refine integral_congr_ae ?_
  filter_upwards [(Lp.coeFn_lpSMul (r := 2) Φ (ftLp f hf))] with θ hθ
  rw [hθ]
  simp only [smul_eq_mul, Pi.mul_apply]

end Work.Maximal
