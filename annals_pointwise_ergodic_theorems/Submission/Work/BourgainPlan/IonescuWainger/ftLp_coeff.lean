import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

/-- The Fourier coefficients of `ftLp h hh` are exactly the sequence `h`: the `m`-th coefficient of
the `L²`-class `Σ_n h n · e_n` along the Hilbert basis `fourierBasis` is `h m`. -/
theorem ftLp_coeff {h : ℤ → ℂ} (hh : Memℓp h 2) (m : ℤ) :
    inner ℂ (fourierBasis (T := 1) m) (ftLp h hh) = h m := by
  rw [← HilbertBasis.repr_apply_apply (fourierBasis (T := 1)) (ftLp h hh) m]
  simp [ftLp]

end Work.BourgainPlan.IonescuWainger
