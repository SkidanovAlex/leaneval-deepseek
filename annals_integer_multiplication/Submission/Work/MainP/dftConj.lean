import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.MainP

open scoped BigOperators

/-- Conjugation of the complex exponential factor of the multidimensional DFT:
for real `φ`, `conj (exp ((-1)·2πi·φ)) = exp (1·2πi·φ)`. -/
private lemma conj_exp_neg_phase (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (((-1 : ℤ) : ℂ) * 2 * (Real.pi : ℂ) * Complex.I * (φ : ℂ)))
      = Complex.exp (((1 : ℤ) : ℂ) * 2 * (Real.pi : ℂ) * Complex.I * (φ : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul]
  simp only [map_ofNat, map_intCast, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Paper Prop 5.2, conjugation trick: the `sgn = 1` transform is the conjugate of the `sgn = -1`
transform of the conjugate vector, i.e. `F*_s u = conj (F_s (conj u))`.

Formally `dftMulti ts sgn u j = (1/T) Σ_k exp(sgn·2πi·phase(j,k)) · u_k` with `T = ts.prod` and
`phase` real-valued, and `starRingEnd ℂ` is complex conjugation; the identity follows from
`starRingEnd ℂ (exp z) = exp ((starRingEnd ℂ) z)`, `starRingEnd ℂ (I) = -I`,
`starRingEnd ℂ ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ)`, additivity/multiplicativity of `starRingEnd ℂ`,
`starRingEnd ℂ (1/(T:ℂ)) = 1/(T:ℂ)`, and `Finset.sum` transport. Pure Mathlib. -/
theorem dftConj (ts : List ℕ) (u : Fin ts.prod → ℂ) (j : Fin ts.prod) :
    HvdH.dftMulti ts 1 u j =
      starRingEnd ℂ (HvdH.dftMulti ts (-1) (fun k => starRingEnd ℂ (u k)) j) := by
  simp only [HvdH.dftMulti]
  rw [map_mul, map_sum]
  congr 1
  · rw [map_div₀, map_one, map_natCast]
  · apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, conj_exp_neg_phase, starRingEnd_self_apply]

end Work.MainP
