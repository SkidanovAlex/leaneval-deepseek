import Mathlib
import Submission.Work.PTCert.TFDefs

namespace Work.PTCert.Fourier

theorem fiber_sum_cSfun {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (sgn : (Fin m → ZMod 2) → ι → ℝ) (nu : ι → (Fin m → ZMod 2))
    (rep : ι → ι) (S : Finset (Fin m)) (xb : ι) :
    (∑ x : {x : ι // rep x = xb}, v x.1 * Submission.PTCert.chiS S (nu x.1) * sgn (nu x.1) (rep x.1))
      = Submission.PTCert.cSfun v sgn nu rep S xb := by
  simp only [Submission.PTCert.cSfun]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [x.2]

end Work.PTCert.Fourier
