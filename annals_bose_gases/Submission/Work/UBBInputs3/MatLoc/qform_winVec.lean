import Mathlib.Data.Complex.BigOperators
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

open scoped BigOperators
open Finset

/-- The single matrix element of the `qform` of a window vector: pulling the two real
profile factors `a = prof p (i-m)`, `b = prof p (j-m)` out of the real part. -/
lemma re_winVec_term (a b : ℝ) (A u v : ℂ) :
    (star ((a : ℂ) * u) * A * ((b : ℂ) * v)).re = a * b * (star u * A * v).re := by
  have h : star ((a : ℂ) * u) * A * ((b : ℂ) * v) = (a : ℂ) * (b : ℂ) * (star u * A * v) := by
    rw [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [h, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem qform_winVec (A : ℤ → ℤ → ℂ) (n p : ℕ) (ψ : ℤ → ℂ) (m : ℤ) :
    Work.UBBInputs3.qform A (Work.UBBInputs3.iRange n)
        (Work.UBBInputs3.winVec p ψ m) (Work.UBBInputs3.winVec p ψ m)
      = ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n,
          (Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m))
            * (star (ψ i) * A i j * ψ j).re := by
  simp only [Work.UBBInputs3.qform, Work.UBBInputs3.winVec]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact re_winVec_term (Work.UBBInputs3.prof p (i - m)) (Work.UBBInputs3.prof p (j - m))
    (A i j) (ψ i) (ψ j)

end Work.UBBInputs3.MatLoc
