import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.hasSum_smul_fourierBasis_ftLp
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_eq_discFourier

namespace Work.Maximal

open MeasureTheory

/-- For a sequence `w` supported in a finite set `F`, the `L²(𝕋)` Fourier transform `ftLp w` is a.e.
equal to the finite trigonometric sum `θ ↦ Σ_{m∈F} w m · e^{2πi m θ}`. -/
theorem ftLp_eq_finset_sum {w : ℤ → ℂ} (F : Finset ℤ) (hw : ∀ m : ℤ, m ∉ F → w m = 0)
    (hw2 : Memℓp w 2) :
    (Work.BourgainPlan.IonescuWainger.ftLp w hw2 : AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun θ => ∑ m ∈ F, w m * fourier m θ := by
  have hsum : Summable fun m : ℤ => ‖w m‖ :=
    summable_of_ne_finset_zero (s := F) (fun m hm => by rw [hw m hm, norm_zero])
  have h := Work.BourgainPlan.IonescuWainger.ftLp_eq_discFourier (ρ := w) hsum hw2
  filter_upwards [h] with θ hθ
  rw [hθ]
  exact Work.BourgainPlan.IonescuWainger.discFourier_eq_sum_of_support hw θ

end Work.Maximal
