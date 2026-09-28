import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.Poisson1D

/-!
# The 1-dimensional Gaussian Poisson summation (shifted, with linear phase)

This reduces the requested identity
`∑_k exp(-π c (k+w)² + 2πi T (k+w)) = c^{-1/2} ∑_m exp(-π (m-T)²/c) exp(2πi m w)`
to the already-proved `Work.HP.Sig2.poisson_shift_gaussian`
(`a = c`, phase parameter `c = T`), the only remaining work being the bookkeeping of the
real-to-complex coercions and of `(c : ℂ)^(1/2) = (√c : ℂ)` for `c > 0`.
-/

namespace Work.HP.Sig2

theorem gauss_poisson_1d (c : ℝ) (hc : 0 < c) (T w : ℝ) :
    (∑' k : ℤ, Complex.exp (-(Real.pi * c) * ((k : ℂ) + (w : ℂ)) ^ 2
        + 2 * Real.pi * Complex.I * (T : ℂ) * ((k : ℂ) + (w : ℂ))))
      = (1 / (Real.sqrt c : ℂ)) *
        ∑' m : ℤ, Complex.exp (-(Real.pi / c) * ((m : ℂ) - (T : ℂ)) ^ 2)
          * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (w : ℂ)) := by
  have h := poisson_shift_gaussian c hc T w
  rw [show (∑' k : ℤ, Complex.exp (-(Real.pi * c) * ((k : ℂ) + (w : ℂ)) ^ 2
        + 2 * Real.pi * Complex.I * (T : ℂ) * ((k : ℂ) + (w : ℂ))))
      = (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * (c : ℂ) * ((k : ℂ) + (w : ℂ)) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (T : ℂ) * ((k : ℂ) + (w : ℂ)))) from
    tsum_congr (fun k => by congr 1; ring)]
  rw [h, show ((c : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt c : ℂ) by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hc.le,
      ← Real.sqrt_eq_rpow]]
  congr 1
  exact tsum_congr (fun m => by congr 1; ring_nf)

end Work.HP.Sig2
