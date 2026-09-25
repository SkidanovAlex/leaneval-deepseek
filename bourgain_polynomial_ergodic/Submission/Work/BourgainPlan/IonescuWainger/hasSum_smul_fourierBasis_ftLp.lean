import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

namespace Work.BourgainPlan.IonescuWainger

/-- The Hilbert-basis expansion of the `L²(𝕋)` Fourier transform `ftLp h hh` of a square-summable
sequence `h : ℤ → ℂ`: the series `Σ_n h n • e_n` converges (in `L²`) to `ftLp h hh`. -/
theorem hasSum_smul_fourierBasis_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) :
    HasSum (fun n : ℤ => h n • fourierBasis (T := 1) n) (ftLp h hh) := by
  simpa [ftLp] using
    (fourierBasis (T := 1)).hasSum_repr_symm (⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2)

end Work.BourgainPlan.IonescuWainger
