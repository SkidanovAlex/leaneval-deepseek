import Mathlib
import Submission.Work.Peluse.SwapC.pboxSum_real_nonneg
import Submission.Work.Peluse.Concat.gowersCS

namespace Work.Peluse.SwapC

/-- The norm form of `pboxSum_real_nonneg`: `pbox` is the real part of `pboxSum`. -/
theorem pbox_eq_re (d : ℕ) (hd : 1 ≤ d) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.LadderP.Swap.pbox d q₁ q₂ M S f
      = (Work.Peluse.LadderP.Swap.pboxSum d q₁ q₂ M S f).re := by
  obtain ⟨r, hr, hsum⟩ := pboxSum_real_nonneg d hd q₁ q₂ M S f hf
  rw [Work.Peluse.LadderP.Swap.pbox, hsum, Complex.norm_of_nonneg hr, Complex.ofReal_re]

end Work.Peluse.SwapC
