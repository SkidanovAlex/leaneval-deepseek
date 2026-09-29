import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.dft1Math
import Submission.Work.SynFFT.bitrevFacts

/-!
# The slice word computes the synthetic transform in natural order
-/

set_option autoImplicit false

namespace Work.SynFFT

theorem fftN_eq_dftN (hbr : Work.SynFFT.MrgBitrevProp) (r t k : ℕ) (sgn : ℤ)
    (u : Arr r) (hr : HvdH.IsPow2 r) (ht : t = 2 ^ k) (htr : t ∣ 2 * r)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    ∀ p, p < t → fftN r t k sgn u p = dftN r t sgn u p := by
  obtain ⟨j, hj1, hrj⟩ := hr
  have hrpos : 0 < r := by rw [hrj]; positivity
  intro p hp
  have hp2 : p < 2 ^ k := by rw [← ht]; exact hp
  have hlev : levels r sgn t k u (bitrev k p) = dftN r t sgn u p :=
    (dftLevels r sgn hrpos hsgn k t ht htr u p hp).symm
  unfold fftN
  rw [hbr r k (levels r sgn t k u) p hp2, hlev]

end Work.SynFFT
