import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.API

/-- The absolute value of HB's test function factors: `‖Hk L K z‖ = e^{-(L-2K) Re z} ‖F2 K z‖`.
Proof: `Hk L K z = exp ((c : ℂ) * z) * F2 K z` with `c = -(L - 2*K)`, then `norm_mul` and
`Complex.norm_exp` (`‖exp w‖ = Real.exp w.re`), and `Complex.re_ofReal_mul`.
Holds for all `L K z`; no side conditions.  No `native_decide`. -/
theorem Hk_norm (L K : ℝ) (z : ℂ) :
    ‖Work.LinnikContract.Hk L K z‖ =
      Real.exp (-(L - 2*K) * z.re) * ‖Work.LinnikContract.F2 K z‖ := by
  rw [Work.LinnikContract.Hk, norm_mul, Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_neg, Complex.re_ofReal_mul]

end Work.LinnikContract.API
